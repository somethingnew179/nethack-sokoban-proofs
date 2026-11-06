import NetHack.Soko22Hazard87.AndIntroBlocks0080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro20250 (p : Pattern) (ha : d119384 p = 1) (hb : d120787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119374 q = 1) (hb : d120778 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119374, d120778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20248 q ha hb
    | true =>
      simp only [d119374, d120778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119375 q = 1) (hb : d120779 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119375, d120779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119375, d120779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119379 q = 1) (hb : d120782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119379, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20249 q ha hb
    | true =>
      simp only [d119379, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119380 q = 1) (hb : d120783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119380, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119380, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119381 q = 1) (hb : d120784 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119381, d120784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119381, d120784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119382 q = 1) (hb : d120785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119382, d120785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119382, d120785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119383 q = 1) (hb : d120786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119383, d120786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119383, d120786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119384 q = 1) (hb : d120787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119384, d120787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119384, d120787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20251 (p : Pattern) (ha : d119367 p = 1) (hb : d120788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119367 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1406 q = 1) (hb : d119359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1406, d119359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1406, d119359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20211 q ha hb
  have h3 (q : Pattern) (ha : d1136 q = 1) (hb : d119182 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1136, d119182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20211 q ha hb
    | true =>
      simp only [d1136, d119182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1407 q = 1) (hb : d119360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1407, d119360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1407, d119360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1137 q = 1) (hb : d119183 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1137, d119183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1137, d119183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1408 q = 1) (hb : d119361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1408, d119361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1408, d119361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1409 q = 1) (hb : d119362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1409, d119362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1409, d119362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1410 q = 1) (hb : d119367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1410, d119367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1410, d119367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d119367 q = 1) (hb : d120788 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro20252 (p : Pattern) (ha : d119386 p = 1) (hb : d120794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119368 q = 1) (hb : d120789 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119368, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20247 q ha hb
    | true =>
      simp only [d119368, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20251 q ha hb
  have h2 (q : Pattern) (ha : d119369 q = 1) (hb : d120790 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119369, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119369, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119370 q = 1) (hb : d120791 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119370, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119370, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119376 q = 1) (hb : d120792 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119376, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119376, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119385 q = 1) (hb : d120793 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119385, d120793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119385, d120793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119386 q = 1) (hb : d120794 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119386, d120794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119386, d120794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20253 (p : Pattern) (ha : d119392 p = 1) (hb : d120800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119379 q = 1) (hb : d120782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119379, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20249 q ha hb
    | true =>
      simp only [d119379, d120782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119380 q = 1) (hb : d120783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119380, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119380, d120783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119387 q = 1) (hb : d120795 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119387, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20252 q ha hb
    | true =>
      simp only [d119387, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119388 q = 1) (hb : d120796 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119388, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119388, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119389 q = 1) (hb : d120797 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119389, d120797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119389, d120797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119390 q = 1) (hb : d120798 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119390, d120798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119390, d120798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119391 q = 1) (hb : d120799 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119391, d120799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119391, d120799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119392 q = 1) (hb : d120800 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119392, d120800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119392, d120800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20254 (p : Pattern) (ha : d119378 p = 1) (hb : d120804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119364 q = 1) (hb : d120772 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119364, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20246 q ha hb
    | true =>
      simp only [d119364, d120772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20247 q ha hb
  have h2 (q : Pattern) (ha : d119365 q = 1) (hb : d120773 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119365, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119365, d120773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119366 q = 1) (hb : d120774 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119366, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119366, d120774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119371 q = 1) (hb : d120775 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119371, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119371, d120775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119368 q = 1) (hb : d120789 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119368, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20247 q ha hb
    | true =>
      simp only [d119368, d120789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20251 q ha hb
  have h7 (q : Pattern) (ha : d119369 q = 1) (hb : d120790 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119369, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119369, d120790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119370 q = 1) (hb : d120791 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119370, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119370, d120791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119376 q = 1) (hb : d120792 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119376, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119376, d120792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119377 q = 1) (hb : d120803 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119377, d120803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119377, d120803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119378 q = 1) (hb : d120804 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119378, d120804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119378, d120804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20255 (p : Pattern) (ha : d119403 p = 1) (hb : d120810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119379 q = 1) (hb : d120805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119379, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20254 q ha hb
    | true =>
      simp only [d119379, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119380 q = 1) (hb : d120806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119380, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119380, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119400 q = 1) (hb : d120807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119400, d120807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119400, d120807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119401 q = 1) (hb : d120808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119401, d120808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119401, d120808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119402 q = 1) (hb : d120809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119402, d120809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119402, d120809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119403 q = 1) (hb : d120810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119403, d120810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119403, d120810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20256 (p : Pattern) (ha : d119409 p = 1) (hb : d120816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119393 q = 1) (hb : d120801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119393, d120801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20250 q ha hb
    | true =>
      simp only [d119393, d120801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20253 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119399 q = 1) (hb : d120802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119399, d120802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119399, d120802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119404 q = 1) (hb : d120811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119404, d120811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20255 q ha hb
    | true =>
      simp only [d119404, d120811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119405 q = 1) (hb : d120812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119405, d120812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119405, d120812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119406 q = 1) (hb : d120813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119406, d120813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119406, d120813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119407 q = 1) (hb : d120814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119407, d120814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119407, d120814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119408 q = 1) (hb : d120815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119408, d120815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119408, d120815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119409 q = 1) (hb : d120816 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119409, d120816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119409, d120816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20257 (p : Pattern) (ha : d119397 p = 1) (hb : d120821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119387 q = 1) (hb : d120795 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119387, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20252 q ha hb
    | true =>
      simp only [d119387, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119388 q = 1) (hb : d120796 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119388, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119388, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119394 q = 1) (hb : d120818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119394, d120818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119394, d120818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119395 q = 1) (hb : d120819 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119395, d120819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119395, d120819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119396 q = 1) (hb : d120820 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119396, d120820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119396, d120820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119397 q = 1) (hb : d120821 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119397, d120821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119397, d120821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20258 (p : Pattern) (ha : d119416 p = 1) (hb : d120827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119411 q = 1) (hb : d120822 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119411, d120822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20257 q ha hb
    | true =>
      simp only [d119411, d120822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119412 q = 1) (hb : d120823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119412, d120823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119412, d120823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119413 q = 1) (hb : d120824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119413, d120824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119413, d120824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119414 q = 1) (hb : d120825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119414, d120825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119414, d120825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119415 q = 1) (hb : d120826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119415, d120826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119415, d120826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119416 q = 1) (hb : d120827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119416, d120827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119416, d120827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20259 (p : Pattern) (ha : d119422 p = 1) (hb : d120833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119218 q = 1) (hb : d120648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119218, d120648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119218, d120648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20217 q ha hb
  have h2 (q : Pattern) (ha : d119219 q = 1) (hb : d120649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119219, d120649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119219, d120649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d119228 q = 1) (hb : d120658 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119228, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20217 q ha hb
    | true =>
      simp only [d119228, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20220 q ha hb
  have h4 (q : Pattern) (ha : d119229 q = 1) (hb : d120659 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119229, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119229, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119230 q = 1) (hb : d120660 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119230, d120660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119230, d120660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119306 q = 1) (hb : d120733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119306, d120733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20232 q ha hb
    | true =>
      simp only [d119306, d120733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20240 q ha hb
  have h7 (q : Pattern) (ha : d119319 q = 1) (hb : d120751 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119319, d120751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20241 q ha hb
    | true =>
      simp only [d119319, d120751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20242 q ha hb
  have h8 (q : Pattern) (ha : d119320 q = 1) (hb : d120752 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119320, d120752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119320, d120752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119321 q = 1) (hb : d120753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119321, d120753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119321, d120753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119322 q = 1) (hb : d120754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119322, d120754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119322, d120754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119326 q = 1) (hb : d120758 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119326, d120758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119326, d120758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20243 q ha hb
  have h12 (q : Pattern) (ha : d119328 q = 1) (hb : d120760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119328, d120760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119328, d120760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20244 q ha hb
  have h13 (q : Pattern) (ha : d119329 q = 1) (hb : d120761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119329, d120761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119329, d120761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119330 q = 1) (hb : d120762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119330, d120762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119330, d120762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d119331 q = 1) (hb : d120763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119331, d120763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d119331, d120763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d119332 q = 1) (hb : d120764 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119332, d120764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119332, d120764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119410 q = 1) (hb : d120817 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119410, d120817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119410, d120817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20256 q ha hb
  have h18 (q : Pattern) (ha : d119417 q = 1) (hb : d120828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119417, d120828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119417, d120828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20258 q ha hb
  have h19 (q : Pattern) (ha : d119418 q = 1) (hb : d120829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119418, d120829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119418, d120829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d119419 q = 1) (hb : d120830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119419, d120830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d119419, d120830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d119420 q = 1) (hb : d120831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119420, d120831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d119420, d120831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d119421 q = 1) (hb : d120832 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119421, d120832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d119421, d120832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d119422 q = 1) (hb : d120833 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d119422, d120833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d119422, d120833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20260 (p : Pattern) (ha : d119428 p = 1) (hb : d120839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119423 q = 1) (hb : d120834 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d119423, d120834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119423, d120834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20259 q ha hb
  have h2 (q : Pattern) (ha : d119424 q = 1) (hb : d120835 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d119424, d120835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119424, d120835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119425 q = 1) (hb : d120836 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d119425, d120836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119425, d120836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119426 q = 1) (hb : d120837 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d119426, d120837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119426, d120837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119427 q = 1) (hb : d120838 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d119427, d120838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119427, d120838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119428 q = 1) (hb : d120839 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d119428, d120839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119428, d120839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20261 (p : Pattern) (ha : d22219 p = 1) (hb : d52994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h5 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h6 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1546 q = 1) (hb : d52987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1546, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1534 q = 1) (hb : d52975 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro201 q ha hb
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1535 q = 1) (hb : d52976 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1551 q = 1) (hb : d52992 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1552 q = 1) (hb : d52993 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1552, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1553 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1553, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d22219 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20262 (p : Pattern) (ha : d22232 p = 1) (hb : d53009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h3 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1560 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h5 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h6 (q : Pattern) (ha : d1561 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1562 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1562, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d1566 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1567 q = 1) (hb : d53008 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1567, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1568 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1568, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d22232 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20263 (p : Pattern) (ha : d119440 p = 1) (hb : d120843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119440 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22220 q = 1) (hb : d119432 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20261 q ha hb
    | true =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22221 q = 1) (hb : d119433 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22222 q = 1) (hb : d119434 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d119434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22222, d119434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22223 q = 1) (hb : d119435 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d119435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22223, d119435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22233 q = 1) (hb : d119436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20262 q ha hb
    | true =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d22234 q = 1) (hb : d119437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22235 q = 1) (hb : d119438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d119438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22235, d119438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22236 q = 1) (hb : d119439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d119439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22236, d119439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22237 q = 1) (hb : d119440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22237, d119440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22237, d119440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119440 q = 1) (hb : d120843 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20264 (p : Pattern) (ha : d119445 p = 1) (hb : d120844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119445 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22233 q = 1) (hb : d119436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20262 q ha hb
    | true =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22234 q = 1) (hb : d119437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22235 q = 1) (hb : d119438 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d119438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22235, d119438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22236 q = 1) (hb : d119439 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d119439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22236, d119439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119444 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22254 q = 1) (hb : d119445 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22254, d119445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22254, d119445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119445 q = 1) (hb : d120844 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro20265 (p : Pattern) (ha : d1596 p = 1) (hb : d53021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h3 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1593 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1593, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1594 q = 1) (hb : d53020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1594, d53020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1594, d53020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1595 q = 1) (hb : d53021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1595, d53021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1595, d53021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53021 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1596 q = 1) (hb : d53021 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20266 (p : Pattern) (ha : d119458 p = 1) (hb : d120849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119458 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1597 q = 1) (hb : d119441 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d119441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20265 q ha hb
    | true =>
      simp only [d1597, d119441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1598 q = 1) (hb : d119442 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d119442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1598, d119442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1599 q = 1) (hb : d119443 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1599, d119443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1599, d119443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1600 q = 1) (hb : d119444 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1600, d119444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1600, d119444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1601 q = 1) (hb : d119458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1601, d119458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1601, d119458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d119458 q = 1) (hb : d120849 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20267 (p : Pattern) (ha : d119464 p = 1) (hb : d120855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119446 q = 1) (hb : d120845 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119446, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20263 q ha hb
    | true =>
      simp only [d119446, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20264 q ha hb
  have h2 (q : Pattern) (ha : d119447 q = 1) (hb : d120846 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119447, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119447, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119448 q = 1) (hb : d120847 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119448, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119448, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119456 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119457 q = 1) (hb : d120848 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119457, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119457, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119459 q = 1) (hb : d120850 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119459, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20264 q ha hb
    | true =>
      simp only [d119459, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20266 q ha hb
  have h7 (q : Pattern) (ha : d119460 q = 1) (hb : d120851 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119460, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119460, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119461 q = 1) (hb : d120852 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119461, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119461, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119462 q = 1) (hb : d120853 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119462, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119462, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119463 q = 1) (hb : d120854 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119463, d120854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119463, d120854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119464 q = 1) (hb : d120855 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119464, d120855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119464, d120855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20268 (p : Pattern) (ha : d119468 p = 1) (hb : d120859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119459 q = 1) (hb : d120850 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119459, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20264 q ha hb
    | true =>
      simp only [d119459, d120850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20266 q ha hb
  have h2 (q : Pattern) (ha : d119460 q = 1) (hb : d120851 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119460, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119460, d120851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119461 q = 1) (hb : d120852 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119461, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119461, d120852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119462 q = 1) (hb : d120853 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119462, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119462, d120853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119467 q = 1) (hb : d120858 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119467, d120858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119467, d120858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119468 q = 1) (hb : d120859 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119468, d120859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119468, d120859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20269 (p : Pattern) (ha : d119474 p = 1) (hb : d120865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119471 q = 1) (hb : d120862 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119472 q = 1) (hb : d120863 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119473 q = 1) (hb : d120864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119473, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119473, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119474 q = 1) (hb : d120865 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119474, d120865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119474, d120865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20270 (p : Pattern) (ha : d119478 p = 1) (hb : d120869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119475 q = 1) (hb : d120866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119476 q = 1) (hb : d120867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119477 q = 1) (hb : d120868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119477, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119477, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119478 q = 1) (hb : d120869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119478, d120869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119478, d120869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20271 (p : Pattern) (ha : d119484 p = 1) (hb : d120875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119479 q = 1) (hb : d120870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20269 q ha hb
    | true =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20270 q ha hb
  have h2 (q : Pattern) (ha : d119480 q = 1) (hb : d120871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119480, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119480, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119481 q = 1) (hb : d120872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119481, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119481, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119482 q = 1) (hb : d120873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119482, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119482, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119483 q = 1) (hb : d120874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119483, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119483, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119484 q = 1) (hb : d120875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119484, d120875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119484, d120875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20272 (p : Pattern) (ha : d119487 p = 1) (hb : d120878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119471 q = 1) (hb : d120862 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119472 q = 1) (hb : d120863 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119473 q = 1) (hb : d120864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119473, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119473, d120864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119487 q = 1) (hb : d120878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119487, d120878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119487, d120878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20273 (p : Pattern) (ha : d119488 p = 1) (hb : d120879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119475 q = 1) (hb : d120866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119476 q = 1) (hb : d120867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119477 q = 1) (hb : d120868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119477, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119477, d120868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119488 q = 1) (hb : d120879 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119488, d120879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119488, d120879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20274 (p : Pattern) (ha : d119494 p = 1) (hb : d120885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119479 q = 1) (hb : d120870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20269 q ha hb
    | true =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20270 q ha hb
  have h2 (q : Pattern) (ha : d119480 q = 1) (hb : d120871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119480, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119480, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119481 q = 1) (hb : d120872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119481, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119481, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119482 q = 1) (hb : d120873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119482, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119482, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119483 q = 1) (hb : d120874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119483, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119483, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119489 q = 1) (hb : d120880 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119489, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20272 q ha hb
    | true =>
      simp only [d119489, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20273 q ha hb
  have h7 (q : Pattern) (ha : d119490 q = 1) (hb : d120881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119490, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119490, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119491 q = 1) (hb : d120882 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119491, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119491, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119492 q = 1) (hb : d120883 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119492, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119492, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119493 q = 1) (hb : d120884 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119493, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119493, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119494 q = 1) (hb : d120885 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119494, d120885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119494, d120885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20275 (p : Pattern) (ha : d119499 p = 1) (hb : d120890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119471 q = 1) (hb : d120862 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119472 q = 1) (hb : d120863 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119498 q = 1) (hb : d120889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119498, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119498, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119499 q = 1) (hb : d120890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119499, d120890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119499, d120890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20276 (p : Pattern) (ha : d119501 p = 1) (hb : d120892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119475 q = 1) (hb : d120866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119476 q = 1) (hb : d120867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119500 q = 1) (hb : d120891 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119500, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119500, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119501 q = 1) (hb : d120892 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119501, d120892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119501, d120892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20277 (p : Pattern) (ha : d119508 p = 1) (hb : d120899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119471 q = 1) (hb : d120862 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119506 q = 1) (hb : d120897 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119506, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119506, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119507 q = 1) (hb : d120898 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119507, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119507, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119508 q = 1) (hb : d120899 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119508, d120899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119508, d120899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20278 (p : Pattern) (ha : d119511 p = 1) (hb : d120902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119475 q = 1) (hb : d120866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119509 q = 1) (hb : d120900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119509, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119509, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119510 q = 1) (hb : d120901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119510, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119510, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119511 q = 1) (hb : d120902 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119511, d120902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119511, d120902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20279 (p : Pattern) (ha : d10035 p = 1) (hb : d52979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h4 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h5 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1530 q = 1) (hb : d52971 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1530, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1204 q = 1) (hb : d52785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro173 q ha hb
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1205 q = 1) (hb : d52786 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1534 q = 1) (hb : d52975 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro201 q ha hb
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1535 q = 1) (hb : d52976 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1536 q = 1) (hb : d52977 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1537 q = 1) (hb : d52978 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1537, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1538 q = 1) (hb : d52979 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1538, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52979 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10035 q = 1) (hb : d52979 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20280 (p : Pattern) (ha : d119519 p = 1) (hb : d120906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119519 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d119515 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d119515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20279 q ha hb
    | true =>
      simp only [d10036, d119515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10038 q = 1) (hb : d119516 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d119516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d119516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d16859 q = 1) (hb : d119517 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d119517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16859, d119517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16860 q = 1) (hb : d119518 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d119518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16860, d119518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22220 q = 1) (hb : d119432 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20261 q ha hb
    | true =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d22221 q = 1) (hb : d119433 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22222 q = 1) (hb : d119434 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d119434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22222, d119434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22223 q = 1) (hb : d119435 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d119435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22223, d119435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22224 q = 1) (hb : d119519 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22224, d119519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22224, d119519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119519 q = 1) (hb : d120906 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20281 (p : Pattern) (ha : d119533 p = 1) (hb : d120912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119520 q = 1) (hb : d120907 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119520, d120907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20280 q ha hb
    | true =>
      simp only [d119520, d120907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20263 q ha hb
  have h2 (q : Pattern) (ha : d119521 q = 1) (hb : d120908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119521, d120908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119521, d120908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119522 q = 1) (hb : d120909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119522, d120909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119522, d120909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119530 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119531 q = 1) (hb : d120910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119531, d120910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119531, d120910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119446 q = 1) (hb : d120845 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119446, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20263 q ha hb
    | true =>
      simp only [d119446, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20264 q ha hb
  have h7 (q : Pattern) (ha : d119447 q = 1) (hb : d120846 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119447, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119447, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119448 q = 1) (hb : d120847 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119448, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119448, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119456 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119457 q = 1) (hb : d120848 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119457, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119457, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119532 q = 1) (hb : d120911 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119532, d120911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119532, d120911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119533 q = 1) (hb : d120912 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119533, d120912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119533, d120912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20282 (p : Pattern) (ha : d119538 p = 1) (hb : d120916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119446 q = 1) (hb : d120845 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119446, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20263 q ha hb
    | true =>
      simp only [d119446, d120845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20264 q ha hb
  have h2 (q : Pattern) (ha : d119447 q = 1) (hb : d120846 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119447, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119447, d120846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119448 q = 1) (hb : d120847 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119448, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119448, d120847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119456 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119457 q = 1) (hb : d120848 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119457, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119457, d120848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119536 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119537 q = 1) (hb : d120915 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119537, d120915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119537, d120915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119538 q = 1) (hb : d120916 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119538, d120916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119538, d120916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20283 (p : Pattern) (ha : d119544 p = 1) (hb : d120922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119534 q = 1) (hb : d120913 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119534, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20281 q ha hb
    | true =>
      simp only [d119534, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119535 q = 1) (hb : d120914 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119535, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119535, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119539 q = 1) (hb : d120917 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20282 q ha hb
    | true =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119540 q = 1) (hb : d120918 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119541 q = 1) (hb : d120919 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119541, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119541, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119542 q = 1) (hb : d120920 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119542, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119542, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119543 q = 1) (hb : d120921 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119543, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119543, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119544 q = 1) (hb : d120922 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119544, d120922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119544, d120922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20284 (p : Pattern) (ha : d119548 p = 1) (hb : d120926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119539 q = 1) (hb : d120917 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20282 q ha hb
    | true =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119540 q = 1) (hb : d120918 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119545 q = 1) (hb : d120923 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119545, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119545, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119546 q = 1) (hb : d120924 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119546, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119546, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119547 q = 1) (hb : d120925 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119547, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119547, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119548 q = 1) (hb : d120926 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119548, d120926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119548, d120926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20285 (p : Pattern) (ha : d119554 p = 1) (hb : d120932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119551 q = 1) (hb : d120929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119551, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119551, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119552 q = 1) (hb : d120930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119552, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119552, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119553 q = 1) (hb : d120931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119553, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119553, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119554 q = 1) (hb : d120932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119554, d120932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119554, d120932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20286 (p : Pattern) (ha : d119560 p = 1) (hb : d120938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119502 q = 1) (hb : d120893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119502, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20275 q ha hb
    | true =>
      simp only [d119502, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20276 q ha hb
  have h2 (q : Pattern) (ha : d119503 q = 1) (hb : d120894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119503, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119503, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119504 q = 1) (hb : d120895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119504, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119504, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119505 q = 1) (hb : d120896 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119505, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119505, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119512 q = 1) (hb : d120903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119512, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20277 q ha hb
    | true =>
      simp only [d119512, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20278 q ha hb
  have h6 (q : Pattern) (ha : d119513 q = 1) (hb : d120904 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119513, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119513, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119514 q = 1) (hb : d120905 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119514, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119514, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119549 q = 1) (hb : d120927 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119549, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20283 q ha hb
    | true =>
      simp only [d119549, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20284 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119479 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119550 q = 1) (hb : d120928 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119550, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119550, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119555 q = 1) (hb : d120933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119555, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20285 q ha hb
    | true =>
      simp only [d119555, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119556 q = 1) (hb : d120934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119556, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119556, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119557 q = 1) (hb : d120935 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119557, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119557, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119558 q = 1) (hb : d120936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119558, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119558, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119559 q = 1) (hb : d120937 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119559, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119559, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119560 q = 1) (hb : d120938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119560, d120938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119560, d120938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20287 (p : Pattern) (ha : d119561 p = 1) (hb : d120939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119471 q = 1) (hb : d120862 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119472 q = 1) (hb : d120863 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119472, d120863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119498 q = 1) (hb : d120889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119498, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119498, d120889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119561 q = 1) (hb : d120939 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119561, d120939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119561, d120939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20288 (p : Pattern) (ha : d119562 p = 1) (hb : d120940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119475 q = 1) (hb : d120866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119476 q = 1) (hb : d120867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119476, d120867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119500 q = 1) (hb : d120891 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119500, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119500, d120891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119562 q = 1) (hb : d120940 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119562, d120940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119562, d120940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20289 (p : Pattern) (ha : d119567 p = 1) (hb : d120945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119471 q = 1) (hb : d120862 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119471, d120862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119506 q = 1) (hb : d120897 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119506, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119506, d120897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119507 q = 1) (hb : d120898 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119507, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119507, d120898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119567 q = 1) (hb : d120945 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119567, d120945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119567, d120945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20290 (p : Pattern) (ha : d119568 p = 1) (hb : d120946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119475 q = 1) (hb : d120866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119475, d120866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119509 q = 1) (hb : d120900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119509, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119509, d120900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119510 q = 1) (hb : d120901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119510, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119510, d120901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119568 q = 1) (hb : d120946 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119568, d120946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119568, d120946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20291 (p : Pattern) (ha : d119572 p = 1) (hb : d120950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119534 q = 1) (hb : d120913 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119534, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20281 q ha hb
    | true =>
      simp only [d119534, d120913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119535 q = 1) (hb : d120914 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119535, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119535, d120914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119539 q = 1) (hb : d120917 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20282 q ha hb
    | true =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119540 q = 1) (hb : d120918 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119541 q = 1) (hb : d120919 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119541, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119541, d120919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119542 q = 1) (hb : d120920 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119542, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119542, d120920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119543 q = 1) (hb : d120921 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119543, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119543, d120921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119572 q = 1) (hb : d120950 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119572, d120950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119572, d120950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20292 (p : Pattern) (ha : d119573 p = 1) (hb : d120951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119539 q = 1) (hb : d120917 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20282 q ha hb
    | true =>
      simp only [d119539, d120917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119540 q = 1) (hb : d120918 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119540, d120918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119469 q = 1) (hb : d120860 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20268 q ha hb
    | true =>
      simp only [d119469, d120860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119470 q = 1) (hb : d120861 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119470, d120861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119545 q = 1) (hb : d120923 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119545, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119545, d120923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119546 q = 1) (hb : d120924 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119546, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119546, d120924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119547 q = 1) (hb : d120925 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119547, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119547, d120925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119573 q = 1) (hb : d120951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119573, d120951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119573, d120951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20293 (p : Pattern) (ha : d119576 p = 1) (hb : d120954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119465 q = 1) (hb : d120856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20267 q ha hb
    | true =>
      simp only [d119465, d120856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119466 q = 1) (hb : d120857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119466, d120857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119551 q = 1) (hb : d120929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119551, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119551, d120929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119552 q = 1) (hb : d120930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119552, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119552, d120930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119553 q = 1) (hb : d120931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119553, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119553, d120931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119576 q = 1) (hb : d120954 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119576, d120954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119576, d120954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20294 (p : Pattern) (ha : d119582 p = 1) (hb : d120960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119502 q = 1) (hb : d120893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119502, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20275 q ha hb
    | true =>
      simp only [d119502, d120893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20276 q ha hb
  have h2 (q : Pattern) (ha : d119503 q = 1) (hb : d120894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119503, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119503, d120894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119504 q = 1) (hb : d120895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119504, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119504, d120895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119505 q = 1) (hb : d120896 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119505, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119505, d120896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119512 q = 1) (hb : d120903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119512, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20277 q ha hb
    | true =>
      simp only [d119512, d120903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20278 q ha hb
  have h6 (q : Pattern) (ha : d119513 q = 1) (hb : d120904 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119513, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119513, d120904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119514 q = 1) (hb : d120905 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119514, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119514, d120905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119549 q = 1) (hb : d120927 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119549, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20283 q ha hb
    | true =>
      simp only [d119549, d120927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20284 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119479 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119550 q = 1) (hb : d120928 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119550, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119550, d120928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119555 q = 1) (hb : d120933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119555, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20285 q ha hb
    | true =>
      simp only [d119555, d120933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119556 q = 1) (hb : d120934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119556, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119556, d120934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119557 q = 1) (hb : d120935 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119557, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119557, d120935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119558 q = 1) (hb : d120936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119558, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119558, d120936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119559 q = 1) (hb : d120937 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119559, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119559, d120937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119563 q = 1) (hb : d120941 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119563, d120941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20287 q ha hb
    | true =>
      simp only [d119563, d120941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20288 q ha hb
  have h17 (q : Pattern) (ha : d119564 q = 1) (hb : d120942 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119564, d120942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119564, d120942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119565 q = 1) (hb : d120943 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119565, d120943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119565, d120943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d119566 q = 1) (hb : d120944 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119566, d120944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119566, d120944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d119569 q = 1) (hb : d120947 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119569, d120947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20289 q ha hb
    | true =>
      simp only [d119569, d120947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20290 q ha hb
  have h21 (q : Pattern) (ha : d119570 q = 1) (hb : d120948 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119570, d120948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119570, d120948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d119571 q = 1) (hb : d120949 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119571, d120949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d119571, d120949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d119574 q = 1) (hb : d120952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119574, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20291 q ha hb
    | true =>
      simp only [d119574, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20292 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d119489 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d119575 q = 1) (hb : d120953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119575, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d119575, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d119577 q = 1) (hb : d120955 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119577, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20293 q ha hb
    | true =>
      simp only [d119577, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d119578 q = 1) (hb : d120956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119578, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d119578, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d119579 q = 1) (hb : d120957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119579, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d119579, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d119580 q = 1) (hb : d120958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119580, d120958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d119580, d120958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d119581 q = 1) (hb : d120959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119581, d120959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d119581, d120959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d119582 q = 1) (hb : d120960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119582, d120960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d119582, d120960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20295 (p : Pattern) (ha : d119594 p = 1) (hb : d120972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119584 q = 1) (hb : d120962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119584, d120962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20284 q ha hb
    | true =>
      simp only [d119584, d120962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20270 q ha hb
  have h2 (q : Pattern) (ha : d119585 q = 1) (hb : d120963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119585, d120963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119585, d120963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119586 q = 1) (hb : d120964 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119586, d120964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119586, d120964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119587 q = 1) (hb : d120965 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119587, d120965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119587, d120965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119588 q = 1) (hb : d120966 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119588, d120966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119588, d120966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119589 q = 1) (hb : d120967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119589, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20270 q ha hb
    | true =>
      simp only [d119589, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119590 q = 1) (hb : d120968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119590, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119590, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119591 q = 1) (hb : d120969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119591, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119591, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119592 q = 1) (hb : d120970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119592, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119592, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119593 q = 1) (hb : d120971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119593, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119593, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119594 q = 1) (hb : d120972 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119594, d120972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119594, d120972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20296 (p : Pattern) (ha : d119600 p = 1) (hb : d120978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119589 q = 1) (hb : d120967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119589, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20270 q ha hb
    | true =>
      simp only [d119589, d120967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119590 q = 1) (hb : d120968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119590, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119590, d120968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119591 q = 1) (hb : d120969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119591, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119591, d120969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119592 q = 1) (hb : d120970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119592, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119592, d120970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119593 q = 1) (hb : d120971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119593, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119593, d120971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119595 q = 1) (hb : d120973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119595, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20273 q ha hb
    | true =>
      simp only [d119595, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119596 q = 1) (hb : d120974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119596, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119596, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119597 q = 1) (hb : d120975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119597, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119597, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119598 q = 1) (hb : d120976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119598, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119598, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119599 q = 1) (hb : d120977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119599, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119599, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119600 q = 1) (hb : d120978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119600, d120978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119600, d120978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20297 (p : Pattern) (ha : d119607 p = 1) (hb : d120985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119574 q = 1) (hb : d120952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119574, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20291 q ha hb
    | true =>
      simp only [d119574, d120952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20292 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119489 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119575 q = 1) (hb : d120953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119575, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119575, d120953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119577 q = 1) (hb : d120955 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119577, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20293 q ha hb
    | true =>
      simp only [d119577, d120955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119578 q = 1) (hb : d120956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119578, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119578, d120956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119579 q = 1) (hb : d120957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119579, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119579, d120957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119605 q = 1) (hb : d120983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119605, d120983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119605, d120983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119606 q = 1) (hb : d120984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119606, d120984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119606, d120984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119607 q = 1) (hb : d120985 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119607, d120985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119607, d120985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20298 (p : Pattern) (ha : d119609 p = 1) (hb : d120987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119595 q = 1) (hb : d120973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119595, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20273 q ha hb
    | true =>
      simp only [d119595, d120973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119596 q = 1) (hb : d120974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119596, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119596, d120974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119597 q = 1) (hb : d120975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119597, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119597, d120975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119598 q = 1) (hb : d120976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119598, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119598, d120976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119599 q = 1) (hb : d120977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119599, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119599, d120977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119609 q = 1) (hb : d120987 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119609, d120987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119609, d120987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20299 (p : Pattern) (ha : d119623 p = 1) (hb : d120993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119623 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17004 q = 1) (hb : d119615 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d119615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17004, d119615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20279 q ha hb
  have h3 (q : Pattern) (ha : d10036 q = 1) (hb : d119515 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d119515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20279 q ha hb
    | true =>
      simp only [d10036, d119515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17005 q = 1) (hb : d119616 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d119616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17005, d119616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10038 q = 1) (hb : d119516 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d119516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10038, d119516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17006 q = 1) (hb : d119617 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d119617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17006, d119617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17007 q = 1) (hb : d119618 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d119618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17007, d119618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22508 q = 1) (hb : d119619 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d119619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22508, d119619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20261 q ha hb
  have h9 (q : Pattern) (ha : d22220 q = 1) (hb : d119432 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20261 q ha hb
    | true =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22509 q = 1) (hb : d119620 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d119620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22509, d119620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22221 q = 1) (hb : d119433 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d22510 q = 1) (hb : d119621 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d119621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22510, d119621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22511 q = 1) (hb : d119622 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d119622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22511, d119622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22512 q = 1) (hb : d119623 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22512, d119623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22512, d119623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119623 q = 1) (hb : d120993 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20300 (p : Pattern) (ha : d119628 p = 1) (hb : d120994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119628 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22508 q = 1) (hb : d119619 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d119619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22508, d119619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20261 q ha hb
  have h3 (q : Pattern) (ha : d22220 q = 1) (hb : d119432 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20261 q ha hb
    | true =>
      simp only [d22220, d119432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22509 q = 1) (hb : d119620 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d119620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22509, d119620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22221 q = 1) (hb : d119433 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22221, d119433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22510 q = 1) (hb : d119621 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d119621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22510, d119621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22511 q = 1) (hb : d119622 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d119622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22511, d119622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22529 q = 1) (hb : d119624 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d119624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22529, d119624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20262 q ha hb
  have h9 (q : Pattern) (ha : d22233 q = 1) (hb : d119436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20262 q ha hb
    | true =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22530 q = 1) (hb : d119625 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d119625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22530, d119625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22234 q = 1) (hb : d119437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d22531 q = 1) (hb : d119626 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d119626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22531, d119626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22532 q = 1) (hb : d119627 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d119627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22532, d119627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22533 q = 1) (hb : d119628 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22533, d119628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22533, d119628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119628 q = 1) (hb : d120994 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20301 (p : Pattern) (ha : d119645 p = 1) (hb : d120999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119645 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22529 q = 1) (hb : d119624 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d119624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22529, d119624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20262 q ha hb
  have h3 (q : Pattern) (ha : d22233 q = 1) (hb : d119436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20262 q ha hb
    | true =>
      simp only [d22233, d119436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22530 q = 1) (hb : d119625 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d119625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22530, d119625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22234 q = 1) (hb : d119437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22234, d119437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22531 q = 1) (hb : d119626 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d119626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22531, d119626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22532 q = 1) (hb : d119627 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d119627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22532, d119627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119644 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22561 q = 1) (hb : d119645 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22561, d119645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22561, d119645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119645 q = 1) (hb : d120999 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro20302 (p : Pattern) (ha : d119659 p = 1) (hb : d121005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119629 q = 1) (hb : d120995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119629, d120995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20299 q ha hb
    | true =>
      simp only [d119629, d120995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20300 q ha hb
  have h2 (q : Pattern) (ha : d119630 q = 1) (hb : d120996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119630, d120996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119630, d120996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119631 q = 1) (hb : d120997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119631, d120997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119631, d120997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119639 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119640 q = 1) (hb : d120998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119640, d120998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119640, d120998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119646 q = 1) (hb : d121000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119646, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20300 q ha hb
    | true =>
      simp only [d119646, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20301 q ha hb
  have h7 (q : Pattern) (ha : d119647 q = 1) (hb : d121001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119647, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119647, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119648 q = 1) (hb : d121002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119648, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119648, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119656 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119657 q = 1) (hb : d121003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119657, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119657, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119658 q = 1) (hb : d121004 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119658, d121004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119658, d121004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119659 q = 1) (hb : d121005 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119659, d121005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119659, d121005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20303 (p : Pattern) (ha : d119664 p = 1) (hb : d121009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119646 q = 1) (hb : d121000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119646, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20300 q ha hb
    | true =>
      simp only [d119646, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20301 q ha hb
  have h2 (q : Pattern) (ha : d119647 q = 1) (hb : d121001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119647, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119647, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119648 q = 1) (hb : d121002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119648, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119648, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119657 q = 1) (hb : d121003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119657, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119657, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119662 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119663 q = 1) (hb : d121008 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119663, d121008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119663, d121008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119664 q = 1) (hb : d121009 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119664, d121009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119664, d121009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20304 (p : Pattern) (ha : d119670 p = 1) (hb : d121015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119660 q = 1) (hb : d121006 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119660, d121006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20302 q ha hb
    | true =>
      simp only [d119660, d121006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119661 q = 1) (hb : d121007 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119661, d121007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119661, d121007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119665 q = 1) (hb : d121010 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119665, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20303 q ha hb
    | true =>
      simp only [d119665, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119666 q = 1) (hb : d121011 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119666, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119666, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119667 q = 1) (hb : d121012 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119667, d121012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119667, d121012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119668 q = 1) (hb : d121013 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119668, d121013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119668, d121013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119669 q = 1) (hb : d121014 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119669, d121014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119669, d121014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119670 q = 1) (hb : d121015 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119670, d121015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119670, d121015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20305 (p : Pattern) (ha : d119671 p = 1) (hb : d121016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119671 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1883 q = 1) (hb : d119641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1883, d119641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1883, d119641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20265 q ha hb
  have h3 (q : Pattern) (ha : d1597 q = 1) (hb : d119441 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d119441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20265 q ha hb
    | true =>
      simp only [d1597, d119441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1884 q = 1) (hb : d119642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1884, d119642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1884, d119642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1598 q = 1) (hb : d119442 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d119442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1598, d119442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1885 q = 1) (hb : d119643 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d119643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1885, d119643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1886 q = 1) (hb : d119644 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d119644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1886, d119644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1887 q = 1) (hb : d119671 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d119671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1887, d119671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d119671 q = 1) (hb : d121016 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro20306 (p : Pattern) (ha : d119677 p = 1) (hb : d121022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119672 q = 1) (hb : d121017 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119672, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20301 q ha hb
    | true =>
      simp only [d119672, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20305 q ha hb
  have h2 (q : Pattern) (ha : d119673 q = 1) (hb : d121018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119673, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119673, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119674 q = 1) (hb : d121019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119674, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119674, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119675 q = 1) (hb : d121020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119675, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119675, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119676 q = 1) (hb : d121021 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119676, d121021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119676, d121021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119677 q = 1) (hb : d121022 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119677, d121022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119677, d121022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20307 (p : Pattern) (ha : d119683 p = 1) (hb : d121028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119665 q = 1) (hb : d121010 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119665, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20303 q ha hb
    | true =>
      simp only [d119665, d121010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119666 q = 1) (hb : d121011 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119666, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119666, d121011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119678 q = 1) (hb : d121023 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119678, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20306 q ha hb
    | true =>
      simp only [d119678, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119679 q = 1) (hb : d121024 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119679, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119679, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119680 q = 1) (hb : d121025 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119680, d121025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119680, d121025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119681 q = 1) (hb : d121026 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119681, d121026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119681, d121026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119682 q = 1) (hb : d121027 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119682, d121027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119682, d121027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119683 q = 1) (hb : d121028 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119683, d121028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119683, d121028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20308 (p : Pattern) (ha : d119686 p = 1) (hb : d121032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119646 q = 1) (hb : d121000 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119646, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20300 q ha hb
    | true =>
      simp only [d119646, d121000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20301 q ha hb
  have h2 (q : Pattern) (ha : d119647 q = 1) (hb : d121001 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119647, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119647, d121001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119648 q = 1) (hb : d121002 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119648, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119648, d121002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119657 q = 1) (hb : d121003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119657, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119657, d121003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119672 q = 1) (hb : d121017 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119672, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20301 q ha hb
    | true =>
      simp only [d119672, d121017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20305 q ha hb
  have h7 (q : Pattern) (ha : d119673 q = 1) (hb : d121018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119673, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119673, d121018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119674 q = 1) (hb : d121019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119674, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119674, d121019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119675 q = 1) (hb : d121020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119675, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119675, d121020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119685 q = 1) (hb : d121031 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119685, d121031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119685, d121031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119686 q = 1) (hb : d121032 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119686, d121032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119686, d121032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20309 (p : Pattern) (ha : d119702 p = 1) (hb : d121038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119687 q = 1) (hb : d121033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119687, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20308 q ha hb
    | true =>
      simp only [d119687, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119688 q = 1) (hb : d121034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119688, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119688, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119699 q = 1) (hb : d121035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119699, d121035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119699, d121035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119700 q = 1) (hb : d121036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119700, d121036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119700, d121036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119701 q = 1) (hb : d121037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119701, d121037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119701, d121037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119702 q = 1) (hb : d121038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119702, d121038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119702, d121038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20310 (p : Pattern) (ha : d119708 p = 1) (hb : d121044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119684 q = 1) (hb : d121029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119684, d121029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20304 q ha hb
    | true =>
      simp only [d119684, d121029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20307 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119698 q = 1) (hb : d121030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119698, d121030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119698, d121030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119703 q = 1) (hb : d121039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119703, d121039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20309 q ha hb
    | true =>
      simp only [d119703, d121039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119704 q = 1) (hb : d121040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119704, d121040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119704, d121040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119705 q = 1) (hb : d121041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119705, d121041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119705, d121041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119706 q = 1) (hb : d121042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119706, d121042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119706, d121042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119707 q = 1) (hb : d121043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119707, d121043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119707, d121043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119708 q = 1) (hb : d121044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119708, d121044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119708, d121044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20311 (p : Pattern) (ha : d119696 p = 1) (hb : d121049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119678 q = 1) (hb : d121023 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119678, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20306 q ha hb
    | true =>
      simp only [d119678, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119679 q = 1) (hb : d121024 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119679, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119679, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119693 q = 1) (hb : d121046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119693, d121046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119693, d121046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119694 q = 1) (hb : d121047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119694, d121047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119694, d121047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119695 q = 1) (hb : d121048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119695, d121048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119695, d121048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119696 q = 1) (hb : d121049 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119696, d121049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119696, d121049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20312 (p : Pattern) (ha : d119715 p = 1) (hb : d121055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119710 q = 1) (hb : d121050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119710, d121050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20311 q ha hb
    | true =>
      simp only [d119710, d121050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119711 q = 1) (hb : d121051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119711, d121051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119711, d121051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119712 q = 1) (hb : d121052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119712, d121052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119712, d121052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119713 q = 1) (hb : d121053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119713, d121053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119713, d121053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119714 q = 1) (hb : d121054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119714, d121054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119714, d121054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119715 q = 1) (hb : d121055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119715, d121055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119715, d121055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20313 (p : Pattern) (ha : d119721 p = 1) (hb : d121061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119485 q = 1) (hb : d120876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119485, d120876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119485, d120876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20271 q ha hb
  have h2 (q : Pattern) (ha : d119486 q = 1) (hb : d120877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119486, d120877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119486, d120877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d119495 q = 1) (hb : d120886 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119495, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20271 q ha hb
    | true =>
      simp only [d119495, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20274 q ha hb
  have h4 (q : Pattern) (ha : d119496 q = 1) (hb : d120887 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119496, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119496, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119497 q = 1) (hb : d120888 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119497, d120888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119497, d120888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119583 q = 1) (hb : d120961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119583, d120961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20286 q ha hb
    | true =>
      simp only [d119583, d120961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20294 q ha hb
  have h7 (q : Pattern) (ha : d119601 q = 1) (hb : d120979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119601, d120979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20295 q ha hb
    | true =>
      simp only [d119601, d120979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20296 q ha hb
  have h8 (q : Pattern) (ha : d119602 q = 1) (hb : d120980 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119602, d120980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119602, d120980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119603 q = 1) (hb : d120981 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119603, d120981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119603, d120981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119604 q = 1) (hb : d120982 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119604, d120982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119604, d120982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119608 q = 1) (hb : d120986 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119608, d120986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119608, d120986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20297 q ha hb
  have h12 (q : Pattern) (ha : d119610 q = 1) (hb : d120988 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119610, d120988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119610, d120988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20298 q ha hb
  have h13 (q : Pattern) (ha : d119611 q = 1) (hb : d120989 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119611, d120989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119611, d120989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119612 q = 1) (hb : d120990 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119612, d120990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119612, d120990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d119613 q = 1) (hb : d120991 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119613, d120991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d119613, d120991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d119614 q = 1) (hb : d120992 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119614, d120992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119614, d120992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119709 q = 1) (hb : d121045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119709, d121045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119709, d121045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20310 q ha hb
  have h18 (q : Pattern) (ha : d119716 q = 1) (hb : d121056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119716, d121056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119716, d121056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20312 q ha hb
  have h19 (q : Pattern) (ha : d119717 q = 1) (hb : d121057 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119717, d121057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119717, d121057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d119718 q = 1) (hb : d121058 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119718, d121058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d119718, d121058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d119719 q = 1) (hb : d121059 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119719, d121059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d119719, d121059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d119720 q = 1) (hb : d121060 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119720, d121060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d119720, d121060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d119721 q = 1) (hb : d121061 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d119721, d121061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d119721, d121061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20314 (p : Pattern) (ha : d119727 p = 1) (hb : d121067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119722 q = 1) (hb : d121062 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d119722, d121062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119722, d121062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20313 q ha hb
  have h2 (q : Pattern) (ha : d119723 q = 1) (hb : d121063 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d119723, d121063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119723, d121063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119724 q = 1) (hb : d121064 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d119724, d121064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119724, d121064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119725 q = 1) (hb : d121065 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d119725, d121065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119725, d121065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119726 q = 1) (hb : d121066 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d119726, d121066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119726, d121066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119727 q = 1) (hb : d121067 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d119727, d121067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119727, d121067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20315 (p : Pattern) (ha : d10363 p = 1) (hb : d53312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h5 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h6 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2026 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2031 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2032 q = 1) (hb : d53311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2032, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2032, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2033 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2033, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2033, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10363 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro20316 (p : Pattern) (ha : d22687 p = 1) (hb : d53330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2041 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h5 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h6 (q : Pattern) (ha : d2044 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2045 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2050 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2051 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d22687 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20317 (p : Pattern) (ha : d119740 p = 1) (hb : d121072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d119732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20315 q ha hb
    | true =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10366 q = 1) (hb : d119733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17153 q = 1) (hb : d119734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d119734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17153, d119734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17154 q = 1) (hb : d119735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d119735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17154, d119735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22688 q = 1) (hb : d119736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20316 q ha hb
    | true =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d22689 q = 1) (hb : d119737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22690 q = 1) (hb : d119738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d119738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22690, d119738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22691 q = 1) (hb : d119739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d119739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22691, d119739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22692 q = 1) (hb : d119740 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22692, d119740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22692, d119740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119740 q = 1) (hb : d121072 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20318 (p : Pattern) (ha : d119745 p = 1) (hb : d121073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119745 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22688 q = 1) (hb : d119736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20316 q ha hb
    | true =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22689 q = 1) (hb : d119737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22690 q = 1) (hb : d119738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d119738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22690, d119738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22691 q = 1) (hb : d119739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d119739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22691, d119739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119744 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22709 q = 1) (hb : d119745 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22709, d119745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22709, d119745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119745 q = 1) (hb : d121073 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro20319 (p : Pattern) (ha : d2079 p = 1) (hb : d53342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h2 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h3 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2076 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2076, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2077 q = 1) (hb : d53341 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2077, d53341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2077, d53341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2078 q = 1) (hb : d53342 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2078, d53342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2078, d53342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53342 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2079 q = 1) (hb : d53342 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d2079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20320 (p : Pattern) (ha : d119758 p = 1) (hb : d121078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119758 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2080 q = 1) (hb : d119741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d119741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20319 q ha hb
    | true =>
      simp only [d2080, d119741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2081 q = 1) (hb : d119742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d119742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2081, d119742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2082 q = 1) (hb : d119743 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2082, d119743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2082, d119743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2083 q = 1) (hb : d119744 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2083, d119744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2083, d119744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2084 q = 1) (hb : d119758 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2084, d119758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2084, d119758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d119758 q = 1) (hb : d121078 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20321 (p : Pattern) (ha : d119764 p = 1) (hb : d121084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119746 q = 1) (hb : d121074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119746, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20317 q ha hb
    | true =>
      simp only [d119746, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20318 q ha hb
  have h2 (q : Pattern) (ha : d119747 q = 1) (hb : d121075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119747, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119747, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119748 q = 1) (hb : d121076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119748, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119748, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119757 q = 1) (hb : d121077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119757, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119757, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119759 q = 1) (hb : d121079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119759, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20318 q ha hb
    | true =>
      simp only [d119759, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20320 q ha hb
  have h7 (q : Pattern) (ha : d119760 q = 1) (hb : d121080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119760, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119760, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119761 q = 1) (hb : d121081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119761, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119761, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119762 q = 1) (hb : d121082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119762, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119762, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119763 q = 1) (hb : d121083 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119763, d121083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119763, d121083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119764 q = 1) (hb : d121084 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119764, d121084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119764, d121084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20322 (p : Pattern) (ha : d119768 p = 1) (hb : d121088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119759 q = 1) (hb : d121079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119759, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20318 q ha hb
    | true =>
      simp only [d119759, d121079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20320 q ha hb
  have h2 (q : Pattern) (ha : d119760 q = 1) (hb : d121080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119760, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119760, d121080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119761 q = 1) (hb : d121081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119761, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119761, d121081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119762 q = 1) (hb : d121082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119762, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119762, d121082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119767 q = 1) (hb : d121087 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119767, d121087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119767, d121087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119768 q = 1) (hb : d121088 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119768, d121088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119768, d121088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20323 (p : Pattern) (ha : d119774 p = 1) (hb : d121094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119771 q = 1) (hb : d121091 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119772 q = 1) (hb : d121092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119773 q = 1) (hb : d121093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119773, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119773, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119774 q = 1) (hb : d121094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119774, d121094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119774, d121094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20324 (p : Pattern) (ha : d119778 p = 1) (hb : d121098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119775 q = 1) (hb : d121095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119776 q = 1) (hb : d121096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119777 q = 1) (hb : d121097 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119777, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119777, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119778 q = 1) (hb : d121098 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119778, d121098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119778, d121098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20325 (p : Pattern) (ha : d119784 p = 1) (hb : d121104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119779 q = 1) (hb : d121099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20323 q ha hb
    | true =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20324 q ha hb
  have h2 (q : Pattern) (ha : d119780 q = 1) (hb : d121100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119780, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119780, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119781 q = 1) (hb : d121101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119781, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119781, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119782 q = 1) (hb : d121102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119782, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119782, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119783 q = 1) (hb : d121103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119783, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119783, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119784 q = 1) (hb : d121104 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119784, d121104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119784, d121104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20326 (p : Pattern) (ha : d119787 p = 1) (hb : d121107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119771 q = 1) (hb : d121091 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119772 q = 1) (hb : d121092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119773 q = 1) (hb : d121093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119773, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119773, d121093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119787 q = 1) (hb : d121107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119787, d121107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119787, d121107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20327 (p : Pattern) (ha : d119788 p = 1) (hb : d121108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119775 q = 1) (hb : d121095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119776 q = 1) (hb : d121096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119777 q = 1) (hb : d121097 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119777, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119777, d121097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119788 q = 1) (hb : d121108 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119788, d121108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119788, d121108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20328 (p : Pattern) (ha : d119794 p = 1) (hb : d121114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119779 q = 1) (hb : d121099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20323 q ha hb
    | true =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20324 q ha hb
  have h2 (q : Pattern) (ha : d119780 q = 1) (hb : d121100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119780, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119780, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119781 q = 1) (hb : d121101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119781, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119781, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119782 q = 1) (hb : d121102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119782, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119782, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119783 q = 1) (hb : d121103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119783, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119783, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119789 q = 1) (hb : d121109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119789, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20326 q ha hb
    | true =>
      simp only [d119789, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20327 q ha hb
  have h7 (q : Pattern) (ha : d119790 q = 1) (hb : d121110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119790, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119790, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119791 q = 1) (hb : d121111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119791, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119791, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119792 q = 1) (hb : d121112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119792, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119792, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119793 q = 1) (hb : d121113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119793, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119793, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119794 q = 1) (hb : d121114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119794, d121114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119794, d121114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20329 (p : Pattern) (ha : d119799 p = 1) (hb : d121119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119771 q = 1) (hb : d121091 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119772 q = 1) (hb : d121092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119798 q = 1) (hb : d121118 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119798, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119798, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119799 q = 1) (hb : d121119 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119799, d121119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119799, d121119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20330 (p : Pattern) (ha : d119801 p = 1) (hb : d121121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119775 q = 1) (hb : d121095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119776 q = 1) (hb : d121096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119800 q = 1) (hb : d121120 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119800, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119800, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119801 q = 1) (hb : d121121 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119801, d121121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119801, d121121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20331 (p : Pattern) (ha : d119808 p = 1) (hb : d121128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119771 q = 1) (hb : d121091 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119806 q = 1) (hb : d121126 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119806, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119806, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119807 q = 1) (hb : d121127 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119807, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119807, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119808 q = 1) (hb : d121128 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119808, d121128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119808, d121128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20332 (p : Pattern) (ha : d119811 p = 1) (hb : d121131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119775 q = 1) (hb : d121095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119809 q = 1) (hb : d121129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119809, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119809, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119810 q = 1) (hb : d121130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119810, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119810, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119811 q = 1) (hb : d121131 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119811, d121131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119811, d121131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20333 (p : Pattern) (ha : d10342 p = 1) (hb : d53291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2010 q = 1) (hb : d53289 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2011 q = 1) (hb : d53290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2012 q = 1) (hb : d53291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53291 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10342 q = 1) (hb : d53291 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20334 (p : Pattern) (ha : d119819 p = 1) (hb : d121135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119819 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d119815 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d119815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20333 q ha hb
    | true =>
      simp only [d10343, d119815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10345 q = 1) (hb : d119816 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d119816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d119816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17225 q = 1) (hb : d119817 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d119817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17225, d119817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17226 q = 1) (hb : d119818 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d119818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17226, d119818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10364 q = 1) (hb : d119732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20315 q ha hb
    | true =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10366 q = 1) (hb : d119733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17153 q = 1) (hb : d119734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d119734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17153, d119734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17154 q = 1) (hb : d119735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d119735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17154, d119735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22685 q = 1) (hb : d119819 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22685, d119819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22685, d119819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119819 q = 1) (hb : d121135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20335 (p : Pattern) (ha : d119828 p = 1) (hb : d121141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119820 q = 1) (hb : d121136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119820, d121136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20334 q ha hb
    | true =>
      simp only [d119820, d121136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20317 q ha hb
  have h2 (q : Pattern) (ha : d119821 q = 1) (hb : d121137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119821, d121137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119821, d121137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119822 q = 1) (hb : d121138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119822, d121138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119822, d121138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119825 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119826 q = 1) (hb : d121139 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119826, d121139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119826, d121139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119746 q = 1) (hb : d121074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119746, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20317 q ha hb
    | true =>
      simp only [d119746, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20318 q ha hb
  have h7 (q : Pattern) (ha : d119747 q = 1) (hb : d121075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119747, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119747, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119748 q = 1) (hb : d121076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119748, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119748, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119756 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119757 q = 1) (hb : d121077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119757, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119757, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119827 q = 1) (hb : d121140 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119827, d121140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119827, d121140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119828 q = 1) (hb : d121141 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119828, d121141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119828, d121141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20336 (p : Pattern) (ha : d119833 p = 1) (hb : d121145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119746 q = 1) (hb : d121074 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119746, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20317 q ha hb
    | true =>
      simp only [d119746, d121074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20318 q ha hb
  have h2 (q : Pattern) (ha : d119747 q = 1) (hb : d121075 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119747, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119747, d121075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119748 q = 1) (hb : d121076 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119748, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119748, d121076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119757 q = 1) (hb : d121077 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119757, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119757, d121077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119831 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119832 q = 1) (hb : d121144 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119832, d121144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119832, d121144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119833 q = 1) (hb : d121145 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119833, d121145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119833, d121145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20337 (p : Pattern) (ha : d119839 p = 1) (hb : d121151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119829 q = 1) (hb : d121142 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119829, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20335 q ha hb
    | true =>
      simp only [d119829, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119830 q = 1) (hb : d121143 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119830, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119830, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119834 q = 1) (hb : d121146 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20336 q ha hb
    | true =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119835 q = 1) (hb : d121147 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119836 q = 1) (hb : d121148 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119836, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119836, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119837 q = 1) (hb : d121149 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119837, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119837, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119838 q = 1) (hb : d121150 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119838, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119838, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119839 q = 1) (hb : d121151 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119839, d121151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119839, d121151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20338 (p : Pattern) (ha : d119843 p = 1) (hb : d121155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119834 q = 1) (hb : d121146 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20336 q ha hb
    | true =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119835 q = 1) (hb : d121147 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119840 q = 1) (hb : d121152 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119840, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119840, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119841 q = 1) (hb : d121153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119841, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119841, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119842 q = 1) (hb : d121154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119842, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119842, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119843 q = 1) (hb : d121155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119843, d121155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119843, d121155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20339 (p : Pattern) (ha : d119849 p = 1) (hb : d121161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119846 q = 1) (hb : d121158 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119846, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119846, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119847 q = 1) (hb : d121159 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119847, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119847, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119848 q = 1) (hb : d121160 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119848, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119848, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119849 q = 1) (hb : d121161 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119849, d121161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119849, d121161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20340 (p : Pattern) (ha : d119855 p = 1) (hb : d121167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119802 q = 1) (hb : d121122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119802, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20329 q ha hb
    | true =>
      simp only [d119802, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20330 q ha hb
  have h2 (q : Pattern) (ha : d119803 q = 1) (hb : d121123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119803, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119803, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119804 q = 1) (hb : d121124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119804, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119804, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119805 q = 1) (hb : d121125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119805, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119805, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119812 q = 1) (hb : d121132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119812, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20331 q ha hb
    | true =>
      simp only [d119812, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20332 q ha hb
  have h6 (q : Pattern) (ha : d119813 q = 1) (hb : d121133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119813, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119813, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119814 q = 1) (hb : d121134 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119814, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119814, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119844 q = 1) (hb : d121156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119844, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20337 q ha hb
    | true =>
      simp only [d119844, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20338 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119845 q = 1) (hb : d121157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119845, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119845, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119850 q = 1) (hb : d121162 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119850, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20339 q ha hb
    | true =>
      simp only [d119850, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119851 q = 1) (hb : d121163 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119851, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119851, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119852 q = 1) (hb : d121164 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119852, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119852, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119853 q = 1) (hb : d121165 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119853, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119853, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119854 q = 1) (hb : d121166 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119854, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119854, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119855 q = 1) (hb : d121167 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119855, d121167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119855, d121167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20341 (p : Pattern) (ha : d119856 p = 1) (hb : d121168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119771 q = 1) (hb : d121091 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119772 q = 1) (hb : d121092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119772, d121092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119798 q = 1) (hb : d121118 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119798, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119798, d121118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119856 q = 1) (hb : d121168 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119856, d121168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119856, d121168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20342 (p : Pattern) (ha : d119857 p = 1) (hb : d121169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119775 q = 1) (hb : d121095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119776 q = 1) (hb : d121096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119776, d121096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119800 q = 1) (hb : d121120 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119800, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119800, d121120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119857 q = 1) (hb : d121169 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119857, d121169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119857, d121169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20343 (p : Pattern) (ha : d119862 p = 1) (hb : d121174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119771 q = 1) (hb : d121091 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119771, d121091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119806 q = 1) (hb : d121126 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119806, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119806, d121126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119807 q = 1) (hb : d121127 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119807, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119807, d121127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119862 q = 1) (hb : d121174 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119862, d121174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119862, d121174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20344 (p : Pattern) (ha : d119863 p = 1) (hb : d121175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119775 q = 1) (hb : d121095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119775, d121095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119809 q = 1) (hb : d121129 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119809, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119809, d121129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119810 q = 1) (hb : d121130 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119810, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119810, d121130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119863 q = 1) (hb : d121175 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119863, d121175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119863, d121175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20345 (p : Pattern) (ha : d119867 p = 1) (hb : d121179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119829 q = 1) (hb : d121142 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119829, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20335 q ha hb
    | true =>
      simp only [d119829, d121142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119830 q = 1) (hb : d121143 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119830, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119830, d121143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119834 q = 1) (hb : d121146 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20336 q ha hb
    | true =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119835 q = 1) (hb : d121147 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119836 q = 1) (hb : d121148 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119836, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119836, d121148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119837 q = 1) (hb : d121149 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119837, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119837, d121149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119838 q = 1) (hb : d121150 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119838, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119838, d121150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119867 q = 1) (hb : d121179 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119867, d121179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119867, d121179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20346 (p : Pattern) (ha : d119868 p = 1) (hb : d121180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119834 q = 1) (hb : d121146 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20336 q ha hb
    | true =>
      simp only [d119834, d121146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119835 q = 1) (hb : d121147 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119835, d121147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119769 q = 1) (hb : d121089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20322 q ha hb
    | true =>
      simp only [d119769, d121089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119770 q = 1) (hb : d121090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119770, d121090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119840 q = 1) (hb : d121152 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119840, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119840, d121152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119841 q = 1) (hb : d121153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119841, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119841, d121153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119842 q = 1) (hb : d121154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119842, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119842, d121154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119868 q = 1) (hb : d121180 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119868, d121180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119868, d121180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20347 (p : Pattern) (ha : d119871 p = 1) (hb : d121183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119765 q = 1) (hb : d121085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20321 q ha hb
    | true =>
      simp only [d119765, d121085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119766 q = 1) (hb : d121086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119766, d121086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119846 q = 1) (hb : d121158 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119846, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119846, d121158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119847 q = 1) (hb : d121159 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119847, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119847, d121159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119848 q = 1) (hb : d121160 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119848, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119848, d121160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119871 q = 1) (hb : d121183 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119871, d121183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119871, d121183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20348 (p : Pattern) (ha : d119877 p = 1) (hb : d121189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119802 q = 1) (hb : d121122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119802, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20329 q ha hb
    | true =>
      simp only [d119802, d121122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20330 q ha hb
  have h2 (q : Pattern) (ha : d119803 q = 1) (hb : d121123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119803, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119803, d121123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119804 q = 1) (hb : d121124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119804, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119804, d121124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119805 q = 1) (hb : d121125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119805, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119805, d121125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119812 q = 1) (hb : d121132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119812, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20331 q ha hb
    | true =>
      simp only [d119812, d121132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20332 q ha hb
  have h6 (q : Pattern) (ha : d119813 q = 1) (hb : d121133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119813, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119813, d121133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119814 q = 1) (hb : d121134 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119814, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119814, d121134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119844 q = 1) (hb : d121156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119844, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20337 q ha hb
    | true =>
      simp only [d119844, d121156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20338 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119845 q = 1) (hb : d121157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119845, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119845, d121157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119850 q = 1) (hb : d121162 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119850, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20339 q ha hb
    | true =>
      simp only [d119850, d121162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119851 q = 1) (hb : d121163 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119851, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119851, d121163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d119852 q = 1) (hb : d121164 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119852, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119852, d121164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119853 q = 1) (hb : d121165 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119853, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119853, d121165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119854 q = 1) (hb : d121166 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119854, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119854, d121166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d119858 q = 1) (hb : d121170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119858, d121170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20341 q ha hb
    | true =>
      simp only [d119858, d121170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20342 q ha hb
  have h17 (q : Pattern) (ha : d119859 q = 1) (hb : d121171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119859, d121171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119859, d121171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119860 q = 1) (hb : d121172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119860, d121172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119860, d121172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d119861 q = 1) (hb : d121173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119861, d121173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119861, d121173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d119864 q = 1) (hb : d121176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119864, d121176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20343 q ha hb
    | true =>
      simp only [d119864, d121176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20344 q ha hb
  have h21 (q : Pattern) (ha : d119865 q = 1) (hb : d121177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119865, d121177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119865, d121177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d119866 q = 1) (hb : d121178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119866, d121178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d119866, d121178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d119869 q = 1) (hb : d121181 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119869, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20345 q ha hb
    | true =>
      simp only [d119869, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20346 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d119789 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d119870 q = 1) (hb : d121182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119870, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d119870, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d119872 q = 1) (hb : d121184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119872, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20347 q ha hb
    | true =>
      simp only [d119872, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d119873 q = 1) (hb : d121185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119873, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d119873, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d119874 q = 1) (hb : d121186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119874, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d119874, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d119875 q = 1) (hb : d121187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119875, d121187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d119875, d121187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d119876 q = 1) (hb : d121188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119876, d121188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d119876, d121188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d119877 q = 1) (hb : d121189 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119877, d121189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d119877, d121189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20349 (p : Pattern) (ha : d119889 p = 1) (hb : d121201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119879 q = 1) (hb : d121191 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119879, d121191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20338 q ha hb
    | true =>
      simp only [d119879, d121191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20324 q ha hb
  have h2 (q : Pattern) (ha : d119880 q = 1) (hb : d121192 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119880, d121192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119880, d121192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119881 q = 1) (hb : d121193 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119881, d121193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119881, d121193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119882 q = 1) (hb : d121194 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119882, d121194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119882, d121194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119883 q = 1) (hb : d121195 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119883, d121195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119883, d121195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119884 q = 1) (hb : d121196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119884, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20324 q ha hb
    | true =>
      simp only [d119884, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119885 q = 1) (hb : d121197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119885, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119885, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119886 q = 1) (hb : d121198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119886, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119886, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119887 q = 1) (hb : d121199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119887, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119887, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119888 q = 1) (hb : d121200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119888, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119888, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119889 q = 1) (hb : d121201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119889, d121201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119889, d121201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20350 (p : Pattern) (ha : d119895 p = 1) (hb : d121207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119884 q = 1) (hb : d121196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119884, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20324 q ha hb
    | true =>
      simp only [d119884, d121196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119885 q = 1) (hb : d121197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119885, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119885, d121197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119886 q = 1) (hb : d121198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119886, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119886, d121198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119887 q = 1) (hb : d121199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119887, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119887, d121199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119888 q = 1) (hb : d121200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119888, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119888, d121200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119890 q = 1) (hb : d121202 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119890, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20327 q ha hb
    | true =>
      simp only [d119890, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119891 q = 1) (hb : d121203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119891, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119891, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119892 q = 1) (hb : d121204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119892, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119892, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119893 q = 1) (hb : d121205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119893, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119893, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119894 q = 1) (hb : d121206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119894, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119894, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119895 q = 1) (hb : d121207 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119895, d121207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119895, d121207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20351 (p : Pattern) (ha : d119902 p = 1) (hb : d121214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119869 q = 1) (hb : d121181 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119869, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20345 q ha hb
    | true =>
      simp only [d119869, d121181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20346 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119870 q = 1) (hb : d121182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119870, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119870, d121182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119872 q = 1) (hb : d121184 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119872, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20347 q ha hb
    | true =>
      simp only [d119872, d121184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119873 q = 1) (hb : d121185 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119873, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119873, d121185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119874 q = 1) (hb : d121186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119874, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119874, d121186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119900 q = 1) (hb : d121212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119900, d121212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119900, d121212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119901 q = 1) (hb : d121213 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119901, d121213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119901, d121213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119902 q = 1) (hb : d121214 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119902, d121214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119902, d121214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20352 (p : Pattern) (ha : d119904 p = 1) (hb : d121216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119890 q = 1) (hb : d121202 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119890, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20327 q ha hb
    | true =>
      simp only [d119890, d121202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119891 q = 1) (hb : d121203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119891, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119891, d121203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119892 q = 1) (hb : d121204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119892, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119892, d121204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119893 q = 1) (hb : d121205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119893, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119893, d121205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119894 q = 1) (hb : d121206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119894, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119894, d121206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119904 q = 1) (hb : d121216 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119904, d121216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119904, d121216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20353 (p : Pattern) (ha : d119918 p = 1) (hb : d121222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119918 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17369 q = 1) (hb : d119910 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d119910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17369, d119910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20333 q ha hb
  have h3 (q : Pattern) (ha : d10343 q = 1) (hb : d119815 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d119815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20333 q ha hb
    | true =>
      simp only [d10343, d119815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17370 q = 1) (hb : d119911 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d119911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17370, d119911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10345 q = 1) (hb : d119816 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d119816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10345, d119816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17371 q = 1) (hb : d119912 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d119912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17371, d119912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17372 q = 1) (hb : d119913 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d119913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17372, d119913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d17376 q = 1) (hb : d119914 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d119914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17376, d119914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20315 q ha hb
  have h9 (q : Pattern) (ha : d10364 q = 1) (hb : d119732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20315 q ha hb
    | true =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d17377 q = 1) (hb : d119915 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d119915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17377, d119915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10366 q = 1) (hb : d119733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d17378 q = 1) (hb : d119916 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d119916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17378, d119916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17379 q = 1) (hb : d119917 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d119917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17379, d119917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22932 q = 1) (hb : d119918 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22932, d119918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22932, d119918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119918 q = 1) (hb : d121222 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20354 (p : Pattern) (ha : d119923 p = 1) (hb : d121223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119923 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17376 q = 1) (hb : d119914 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d119914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17376, d119914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20315 q ha hb
  have h3 (q : Pattern) (ha : d10364 q = 1) (hb : d119732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20315 q ha hb
    | true =>
      simp only [d10364, d119732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17377 q = 1) (hb : d119915 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d119915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17377, d119915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10366 q = 1) (hb : d119733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10366, d119733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17378 q = 1) (hb : d119916 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d119916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17378, d119916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17379 q = 1) (hb : d119917 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d119917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17379, d119917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22943 q = 1) (hb : d119919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d119919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22943, d119919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20316 q ha hb
  have h9 (q : Pattern) (ha : d22688 q = 1) (hb : d119736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20316 q ha hb
    | true =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d22944 q = 1) (hb : d119920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d119920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22944, d119920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22689 q = 1) (hb : d119737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d22945 q = 1) (hb : d119921 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d119921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22945, d119921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22946 q = 1) (hb : d119922 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d119922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22946, d119922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d22947 q = 1) (hb : d119923 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22947, d119923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22947, d119923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d119923 q = 1) (hb : d121223 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro20355 (p : Pattern) (ha : d119935 p = 1) (hb : d121228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22943 q = 1) (hb : d119919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d119919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22943, d119919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20316 q ha hb
  have h3 (q : Pattern) (ha : d22688 q = 1) (hb : d119736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20316 q ha hb
    | true =>
      simp only [d22688, d119736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d22944 q = 1) (hb : d119920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d119920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22944, d119920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22689 q = 1) (hb : d119737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22689, d119737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22945 q = 1) (hb : d119921 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d119921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22945, d119921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22946 q = 1) (hb : d119922 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d119922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22946, d119922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119934 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d22975 q = 1) (hb : d119935 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22975, d119935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22975, d119935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119935 q = 1) (hb : d121228 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro20356 (p : Pattern) (ha : d119949 p = 1) (hb : d121234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119924 q = 1) (hb : d121224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119924, d121224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20353 q ha hb
    | true =>
      simp only [d119924, d121224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20354 q ha hb
  have h2 (q : Pattern) (ha : d119925 q = 1) (hb : d121225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119925, d121225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119925, d121225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119926 q = 1) (hb : d121226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119926, d121226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119926, d121226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119930 q = 1) (hb : d121227 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119930, d121227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119930, d121227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119936 q = 1) (hb : d121229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119936, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20354 q ha hb
    | true =>
      simp only [d119936, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20355 q ha hb
  have h7 (q : Pattern) (ha : d119937 q = 1) (hb : d121230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119937, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119937, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119938 q = 1) (hb : d121231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119938, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119938, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119946 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d119947 q = 1) (hb : d121232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119947, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119947, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d119948 q = 1) (hb : d121233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119948, d121233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119948, d121233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d119949 q = 1) (hb : d121234 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119949, d121234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119949, d121234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro20357 (p : Pattern) (ha : d119954 p = 1) (hb : d121238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119936 q = 1) (hb : d121229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119936, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20354 q ha hb
    | true =>
      simp only [d119936, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20355 q ha hb
  have h2 (q : Pattern) (ha : d119937 q = 1) (hb : d121230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119937, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119937, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119938 q = 1) (hb : d121231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119938, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119938, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119946 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119947 q = 1) (hb : d121232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119947, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119947, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119952 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119953 q = 1) (hb : d121237 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119953, d121237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119953, d121237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119954 q = 1) (hb : d121238 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119954, d121238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119954, d121238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20358 (p : Pattern) (ha : d119960 p = 1) (hb : d121244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119950 q = 1) (hb : d121235 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119950, d121235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20356 q ha hb
    | true =>
      simp only [d119950, d121235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119951 q = 1) (hb : d121236 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119951, d121236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119951, d121236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119955 q = 1) (hb : d121239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119955, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20357 q ha hb
    | true =>
      simp only [d119955, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119956 q = 1) (hb : d121240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119956, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119956, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119957 q = 1) (hb : d121241 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119957, d121241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119957, d121241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119958 q = 1) (hb : d121242 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119958, d121242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119958, d121242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119959 q = 1) (hb : d121243 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119959, d121243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119959, d121243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119960 q = 1) (hb : d121244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119960, d121244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119960, d121244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20359 (p : Pattern) (ha : d119961 p = 1) (hb : d121245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119961 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2361 q = 1) (hb : d119931 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d119931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2361, d119931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20319 q ha hb
  have h3 (q : Pattern) (ha : d2080 q = 1) (hb : d119741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d119741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20319 q ha hb
    | true =>
      simp only [d2080, d119741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2362 q = 1) (hb : d119932 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d119932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2362, d119932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2081 q = 1) (hb : d119742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d119742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2081, d119742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2363 q = 1) (hb : d119933 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d119933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2363, d119933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2364 q = 1) (hb : d119934 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d119934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2364, d119934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2365 q = 1) (hb : d119961 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d119961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2365, d119961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d119961 q = 1) (hb : d121245 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d121245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d121245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro20360 (p : Pattern) (ha : d119967 p = 1) (hb : d121251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119962 q = 1) (hb : d121246 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119962, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20355 q ha hb
    | true =>
      simp only [d119962, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20359 q ha hb
  have h2 (q : Pattern) (ha : d119963 q = 1) (hb : d121247 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119963, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119963, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119964 q = 1) (hb : d121248 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119964, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119964, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119965 q = 1) (hb : d121249 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119965, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119965, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119966 q = 1) (hb : d121250 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119966, d121250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119966, d121250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119967 q = 1) (hb : d121251 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119967, d121251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119967, d121251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20361 (p : Pattern) (ha : d119973 p = 1) (hb : d121257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119955 q = 1) (hb : d121239 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119955, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20357 q ha hb
    | true =>
      simp only [d119955, d121239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119956 q = 1) (hb : d121240 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119956, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119956, d121240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119968 q = 1) (hb : d121252 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119968, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20360 q ha hb
    | true =>
      simp only [d119968, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119969 q = 1) (hb : d121253 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119969, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119969, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119970 q = 1) (hb : d121254 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119970, d121254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119970, d121254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119971 q = 1) (hb : d121255 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119971, d121255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119971, d121255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119972 q = 1) (hb : d121256 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119972, d121256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119972, d121256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119973 q = 1) (hb : d121257 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119973, d121257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119973, d121257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20362 (p : Pattern) (ha : d119976 p = 1) (hb : d121261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119936 q = 1) (hb : d121229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119936, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20354 q ha hb
    | true =>
      simp only [d119936, d121229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20355 q ha hb
  have h2 (q : Pattern) (ha : d119937 q = 1) (hb : d121230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119937, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119937, d121230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119938 q = 1) (hb : d121231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119938, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119938, d121231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119946 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119947 q = 1) (hb : d121232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119947, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119947, d121232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119962 q = 1) (hb : d121246 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119962, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20355 q ha hb
    | true =>
      simp only [d119962, d121246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20359 q ha hb
  have h7 (q : Pattern) (ha : d119963 q = 1) (hb : d121247 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119963, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119963, d121247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119964 q = 1) (hb : d121248 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119964, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119964, d121248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119965 q = 1) (hb : d121249 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119965, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119965, d121249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119975 q = 1) (hb : d121260 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119975, d121260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119975, d121260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119976 q = 1) (hb : d121261 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119976, d121261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119976, d121261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro20363 (p : Pattern) (ha : d119992 p = 1) (hb : d121267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119977 q = 1) (hb : d121262 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119977, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20362 q ha hb
    | true =>
      simp only [d119977, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119978 q = 1) (hb : d121263 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119978, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119978, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119989 q = 1) (hb : d121264 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119989, d121264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119989, d121264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119990 q = 1) (hb : d121265 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119990, d121265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119990, d121265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119991 q = 1) (hb : d121266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119991, d121266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119991, d121266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119992 q = 1) (hb : d121267 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119992, d121267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119992, d121267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20364 (p : Pattern) (ha : d119998 p = 1) (hb : d121273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119974 q = 1) (hb : d121258 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119974, d121258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20358 q ha hb
    | true =>
      simp only [d119974, d121258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20361 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119987 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119988 q = 1) (hb : d121259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119988, d121259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119988, d121259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d119993 q = 1) (hb : d121268 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119993, d121268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20363 q ha hb
    | true =>
      simp only [d119993, d121268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119994 q = 1) (hb : d121269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119994, d121269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119994, d121269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119995 q = 1) (hb : d121270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119995, d121270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119995, d121270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119996 q = 1) (hb : d121271 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119996, d121271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119996, d121271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119997 q = 1) (hb : d121272 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119997, d121272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119997, d121272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119998 q = 1) (hb : d121273 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119998, d121273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119998, d121273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20365 (p : Pattern) (ha : d119986 p = 1) (hb : d121278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119968 q = 1) (hb : d121252 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119968, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20360 q ha hb
    | true =>
      simp only [d119968, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119969 q = 1) (hb : d121253 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119969, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119969, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119983 q = 1) (hb : d121275 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119983, d121275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119983, d121275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119984 q = 1) (hb : d121276 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119984, d121276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119984, d121276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119985 q = 1) (hb : d121277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119985, d121277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119985, d121277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119986 q = 1) (hb : d121278 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119986, d121278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119986, d121278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20366 (p : Pattern) (ha : d120005 p = 1) (hb : d121284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120000 q = 1) (hb : d121279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120000, d121279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20365 q ha hb
    | true =>
      simp only [d120000, d121279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120001 q = 1) (hb : d121280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120001, d121280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120001, d121280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120002 q = 1) (hb : d121281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120002, d121281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120002, d121281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120003 q = 1) (hb : d121282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120003, d121282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120003, d121282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120004 q = 1) (hb : d121283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120004, d121283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120004, d121283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120005 q = 1) (hb : d121284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120005, d121284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120005, d121284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20367 (p : Pattern) (ha : d120011 p = 1) (hb : d121290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119785 q = 1) (hb : d121105 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119785, d121105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119785, d121105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20325 q ha hb
  have h2 (q : Pattern) (ha : d119786 q = 1) (hb : d121106 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119786, d121106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119786, d121106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d119795 q = 1) (hb : d121115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119795, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20325 q ha hb
    | true =>
      simp only [d119795, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20328 q ha hb
  have h4 (q : Pattern) (ha : d119796 q = 1) (hb : d121116 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119796, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119796, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119797 q = 1) (hb : d121117 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119797, d121117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119797, d121117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119878 q = 1) (hb : d121190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119878, d121190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20340 q ha hb
    | true =>
      simp only [d119878, d121190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20348 q ha hb
  have h7 (q : Pattern) (ha : d119896 q = 1) (hb : d121208 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119896, d121208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20349 q ha hb
    | true =>
      simp only [d119896, d121208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20350 q ha hb
  have h8 (q : Pattern) (ha : d119897 q = 1) (hb : d121209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119897, d121209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119897, d121209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119898 q = 1) (hb : d121210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119898, d121210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119898, d121210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d119899 q = 1) (hb : d121211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119899, d121211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119899, d121211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119903 q = 1) (hb : d121215 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119903, d121215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119903, d121215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20351 q ha hb
  have h12 (q : Pattern) (ha : d119905 q = 1) (hb : d121217 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119905, d121217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119905, d121217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20352 q ha hb
  have h13 (q : Pattern) (ha : d119906 q = 1) (hb : d121218 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119906, d121218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d119906, d121218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d119907 q = 1) (hb : d121219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119907, d121219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119907, d121219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d119908 q = 1) (hb : d121220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119908, d121220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d119908, d121220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d119909 q = 1) (hb : d121221 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119909, d121221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119909, d121221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119999 q = 1) (hb : d121274 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119999, d121274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119999, d121274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20364 q ha hb
  have h18 (q : Pattern) (ha : d120006 q = 1) (hb : d121285 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120006, d121285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120006, d121285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20366 q ha hb
  have h19 (q : Pattern) (ha : d120007 q = 1) (hb : d121286 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120007, d121286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d120007, d121286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d120008 q = 1) (hb : d121287 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120008, d121287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d120008, d121287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d120009 q = 1) (hb : d121288 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120009, d121288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d120009, d121288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d120010 q = 1) (hb : d121289 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d120010, d121289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d120010, d121289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d120011 q = 1) (hb : d121290 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d120011, d121290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d120011, d121290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20368 (p : Pattern) (ha : d120017 p = 1) (hb : d121296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120012 q = 1) (hb : d121291 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d120012, d121291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120012, d121291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20367 q ha hb
  have h2 (q : Pattern) (ha : d120013 q = 1) (hb : d121292 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d120013, d121292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120013, d121292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120014 q = 1) (hb : d121293 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d120014, d121293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120014, d121293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120015 q = 1) (hb : d121294 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d120015, d121294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120015, d121294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120016 q = 1) (hb : d121295 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d120016, d121295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120016, d121295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120017 q = 1) (hb : d121296 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d120017, d121296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120017, d121296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20369 (p : Pattern) (ha : d120023 p = 1) (hb : d121302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d118942 q = 1) (hb : d120391 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d118942, d120391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20128 q ha hb
    | true =>
      simp only [d118942, d120391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20159 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119171 q = 1) (hb : d120613 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d119171, d120613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119171, d120613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20206 q ha hb
  have h3 (q : Pattern) (ha : d119172 q = 1) (hb : d120614 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d119172, d120614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d119172, d120614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119429 q = 1) (hb : d120840 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d119429, d120840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119429, d120840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20260 q ha hb
  have h5 (q : Pattern) (ha : d119430 q = 1) (hb : d120841 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d119430, d120841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119430, d120841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119431 q = 1) (hb : d120842 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d119431, d120842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119431, d120842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119728 q = 1) (hb : d121068 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d119728, d121068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119728, d121068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20314 q ha hb
  have h8 (q : Pattern) (ha : d119729 q = 1) (hb : d121069 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d119729, d121069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119729, d121069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119730 q = 1) (hb : d121070 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d119730, d121070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119730, d121070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119731 q = 1) (hb : d121071 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d119731, d121071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119731, d121071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120018 q = 1) (hb : d121297 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d120018, d121297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120018, d121297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20368 q ha hb
  have h12 (q : Pattern) (ha : d120019 q = 1) (hb : d121298 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d120019, d121298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120019, d121298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d120020 q = 1) (hb : d121299 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d120020, d121299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120020, d121299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d120021 q = 1) (hb : d121300 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d120021, d121300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120021, d121300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d120022 q = 1) (hb : d121301 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d120022, d121301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120022, d121301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120023 q = 1) (hb : d121302 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d120023, d121302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d120023, d121302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro20370 (p : Pattern) (ha : d120029 p = 1) (hb : d121308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120024 q = 1) (hb : d121303 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d120024, d121303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20369 q ha hb
    | true =>
      simp only [d120024, d121303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120025 q = 1) (hb : d121304 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d120025, d121304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120025, d121304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120026 q = 1) (hb : d121305 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d120026, d121305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120026, d121305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120027 q = 1) (hb : d121306 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d120027, d121306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120027, d121306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120028 q = 1) (hb : d121307 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d120028, d121307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120028, d121307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120029 q = 1) (hb : d121308 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d120029, d121308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120029, d121308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20371 (p : Pattern) (ha : d120035 p = 1) (hb : d121314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120030 q = 1) (hb : d121309 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d120030, d121309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20370 q ha hb
    | true =>
      simp only [d120030, d121309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120031 q = 1) (hb : d121310 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d120031, d121310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120031, d121310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120032 q = 1) (hb : d121311 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d120032, d121311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120032, d121311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120033 q = 1) (hb : d121312 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d120033, d121312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120033, d121312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120034 q = 1) (hb : d121313 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d120034, d121313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120034, d121313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120035 q = 1) (hb : d121314 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d120035, d121314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120035, d121314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20372 (p : Pattern) (ha : d120041 p = 1) (hb : d121320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120036 q = 1) (hb : d121315 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d120036, d121315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20371 q ha hb
    | true =>
      simp only [d120036, d121315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120037 q = 1) (hb : d121316 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d120037, d121316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120037, d121316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120038 q = 1) (hb : d121317 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d120038, d121317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120038, d121317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120039 q = 1) (hb : d121318 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d120039, d121318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120039, d121318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120040 q = 1) (hb : d121319 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d120040, d121319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120040, d121319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120041 q = 1) (hb : d121320 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d120041, d121320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120041, d121320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20373 (p : Pattern) (ha : d120047 p = 1) (hb : d121326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120042 q = 1) (hb : d121321 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d120042, d121321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20372 q ha hb
    | true =>
      simp only [d120042, d121321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120043 q = 1) (hb : d121322 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d120043, d121322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120043, d121322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120044 q = 1) (hb : d121323 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d120044, d121323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120044, d121323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120045 q = 1) (hb : d121324 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d120045, d121324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120045, d121324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120046 q = 1) (hb : d121325 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d120046, d121325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120046, d121325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120047 q = 1) (hb : d121326 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d120047, d121326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120047, d121326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20374 (p : Pattern) (ha : d120053 p = 1) (hb : d121332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120048 q = 1) (hb : d121327 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d120048, d121327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20373 q ha hb
    | true =>
      simp only [d120048, d121327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120049 q = 1) (hb : d121328 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d120049, d121328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120049, d121328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120050 q = 1) (hb : d121329 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d120050, d121329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120050, d121329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120051 q = 1) (hb : d121330 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d120051, d121330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120051, d121330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120052 q = 1) (hb : d121331 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d120052, d121331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120052, d121331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120053 q = 1) (hb : d121332 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d120053, d121332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120053, d121332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20375 (p : Pattern) (ha : d120059 p = 1) (hb : d121338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120054 q = 1) (hb : d121333 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d120054, d121333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20374 q ha hb
    | true =>
      simp only [d120054, d121333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120055 q = 1) (hb : d121334 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d120055, d121334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120055, d121334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120056 q = 1) (hb : d121335 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d120056, d121335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120056, d121335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120057 q = 1) (hb : d121336 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d120057, d121336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120057, d121336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120058 q = 1) (hb : d121337 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d120058, d121337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120058, d121337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120059 q = 1) (hb : d121338 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d120059, d121338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120059, d121338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20376 (p : Pattern) (ha : d120065 p = 1) (hb : d121344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120060 q = 1) (hb : d121339 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d120060, d121339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20375 q ha hb
    | true =>
      simp only [d120060, d121339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120061 q = 1) (hb : d121340 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d120061, d121340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120061, d121340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120062 q = 1) (hb : d121341 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d120062, d121341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120062, d121341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120063 q = 1) (hb : d121342 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d120063, d121342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120063, d121342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120064 q = 1) (hb : d121343 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d120064, d121343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120064, d121343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120065 q = 1) (hb : d121344 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d120065, d121344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120065, d121344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20377 (p : Pattern) (ha : d53647 p = 1) (hb : d116753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19773 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19774 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19792 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19793 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20378 (p : Pattern) (ha : d94521 p = 1) (hb : d116753 p = 1) : d120334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8246 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19784 q ha hb
    | true =>
      simp only [d8246, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
  have h2 (q : Pattern) (ha : d8292 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8293 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8293, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8294 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8295 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94521 q = 1) (hb : d116753 q = 1) : d120334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94521, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94521, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20379 (p : Pattern) (ha : d94531 p = 1) (hb : d116753 p = 1) : d120378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8268 q = 1) (hb : d116753 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19789 q ha hb
    | true =>
      simp only [d8268, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19770 q ha hb
  have h2 (q : Pattern) (ha : d94527 q = 1) (hb : d116753 q = 1) : d120374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94527, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94527, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94528 q = 1) (hb : d116753 q = 1) : d120375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94528, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94528, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94529 q = 1) (hb : d116753 q = 1) : d120376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94529, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94529, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94530 q = 1) (hb : d116753 q = 1) : d120377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94530, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94530, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94531 q = 1) (hb : d116753 q = 1) : d120378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94531, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94531, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20380 (p : Pattern) (ha : d94537 p = 1) (hb : d116753 p = 1) : d121355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8297 q = 1) (hb : d116753 q = 1) : d120144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19794 q ha hb
    | true =>
      simp only [d8297, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19795 q ha hb
  have h2 (q : Pattern) (ha : d8298 q = 1) (hb : d116753 q = 1) : d120145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8298, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94519 q = 1) (hb : d116753 q = 1) : d121345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94519, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94519, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94520 q = 1) (hb : d116753 q = 1) : d121346 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94520, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94520, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94522 q = 1) (hb : d116753 q = 1) : d120335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94522, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94522, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20378 q ha hb
  have h6 (q : Pattern) (ha : d94523 q = 1) (hb : d116753 q = 1) : d121347 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94523, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94523, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94524 q = 1) (hb : d116753 q = 1) : d121348 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94524, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94524, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94525 q = 1) (hb : d116753 q = 1) : d121349 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94525, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94525, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94526 q = 1) (hb : d116753 q = 1) : d121350 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94526, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94526, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94532 q = 1) (hb : d116753 q = 1) : d120379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94532, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94532, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20379 q ha hb
  have h11 (q : Pattern) (ha : d94533 q = 1) (hb : d116753 q = 1) : d121351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94533, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94533, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94534 q = 1) (hb : d116753 q = 1) : d121352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94534, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94534, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94535 q = 1) (hb : d116753 q = 1) : d121353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94535, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94535, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94536 q = 1) (hb : d116753 q = 1) : d121354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94536, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94536, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94537 q = 1) (hb : d116753 q = 1) : d121355 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94537, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94537, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20381 (p : Pattern) (ha : d94543 p = 1) (hb : d116753 p = 1) : d121361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20377 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94538 q = 1) (hb : d116753 q = 1) : d121356 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94538, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94538, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20380 q ha hb
  have h7 (q : Pattern) (ha : d94539 q = 1) (hb : d116753 q = 1) : d121357 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94539, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94539, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94540 q = 1) (hb : d116753 q = 1) : d121358 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94540, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94540, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94541 q = 1) (hb : d116753 q = 1) : d121359 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94541, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94541, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94542 q = 1) (hb : d116753 q = 1) : d121360 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94542, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94542, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94543 q = 1) (hb : d116753 q = 1) : d121361 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94543, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94543, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20382 (p : Pattern) (ha : d94546 p = 1) (hb : d116753 p = 1) : d121364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8430 q = 1) (hb : d116753 q = 1) : d120188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19828 q ha hb
    | true =>
      simp only [d8430, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19820 q ha hb
  have h2 (q : Pattern) (ha : d8431 q = 1) (hb : d116753 q = 1) : d120246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8432 q = 1) (hb : d116753 q = 1) : d120247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8432, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8433 q = 1) (hb : d116753 q = 1) : d120248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8434 q = 1) (hb : d116753 q = 1) : d120249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94546 q = 1) (hb : d116753 q = 1) : d121364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94546, d121364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94546, d121364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20383 (p : Pattern) (ha : d94555 p = 1) (hb : d116753 p = 1) : d120220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d116753 q = 1) : d120215 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19812 q ha hb
    | true =>
      simp only [d8378, d120215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d116753 q = 1) : d120216 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d120216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19823 q ha hb
    | true =>
      simp only [d684, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94552 q = 1) (hb : d116753 q = 1) : d120217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94552, d120217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94552, d120217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94553 q = 1) (hb : d116753 q = 1) : d120218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94553, d120218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94553, d120218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94554 q = 1) (hb : d116753 q = 1) : d120219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94554, d120219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94554, d120219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94555 q = 1) (hb : d116753 q = 1) : d120220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94555, d120220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94555, d120220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20384 (p : Pattern) (ha : d94561 p = 1) (hb : d116753 p = 1) : d121374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94556 q = 1) (hb : d116753 q = 1) : d120221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94556, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20383 q ha hb
    | true =>
      simp only [d94556, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19824 q ha hb
  have h2 (q : Pattern) (ha : d94557 q = 1) (hb : d116753 q = 1) : d121370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94557, d121370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94557, d121370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94558 q = 1) (hb : d116753 q = 1) : d121371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94558, d121371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94558, d121371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94559 q = 1) (hb : d116753 q = 1) : d121372 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94559, d121372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94559, d121372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94560 q = 1) (hb : d116753 q = 1) : d121373 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94560, d121373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94560, d121373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94561 q = 1) (hb : d116753 q = 1) : d121374 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94561, d121374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94561, d121374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20385 (p : Pattern) (ha : d94567 p = 1) (hb : d116753 p = 1) : d121380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d116753 q = 1) : d120251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19827 q ha hb
    | true =>
      simp only [d8436, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19829 q ha hb
  have h2 (q : Pattern) (ha : d8437 q = 1) (hb : d116753 q = 1) : d120252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94544 q = 1) (hb : d116753 q = 1) : d121362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94544, d121362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94544, d121362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94545 q = 1) (hb : d116753 q = 1) : d121363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94545, d121363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94545, d121363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94547 q = 1) (hb : d116753 q = 1) : d121365 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94547, d121365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94547, d121365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20382 q ha hb
  have h6 (q : Pattern) (ha : d94548 q = 1) (hb : d116753 q = 1) : d121366 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94548, d121366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94548, d121366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94549 q = 1) (hb : d116753 q = 1) : d121367 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94549, d121367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94549, d121367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94550 q = 1) (hb : d116753 q = 1) : d121368 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94550, d121368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94550, d121368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94551 q = 1) (hb : d116753 q = 1) : d121369 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94551, d121369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94551, d121369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94562 q = 1) (hb : d116753 q = 1) : d121375 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94562, d121375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94562, d121375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20384 q ha hb
  have h11 (q : Pattern) (ha : d94563 q = 1) (hb : d116753 q = 1) : d121376 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94563, d121376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94563, d121376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94564 q = 1) (hb : d116753 q = 1) : d121377 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94564, d121377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94564, d121377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94565 q = 1) (hb : d116753 q = 1) : d121378 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94565, d121378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94565, d121378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94566 q = 1) (hb : d116753 q = 1) : d121379 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94566, d121379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94566, d121379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94567 q = 1) (hb : d116753 q = 1) : d121380 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94567, d121380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94567, d121380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20386 (p : Pattern) (ha : d94573 p = 1) (hb : d116753 p = 1) : d121386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94568 q = 1) (hb : d116753 q = 1) : d121381 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94568, d121381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94568, d121381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20385 q ha hb
  have h2 (q : Pattern) (ha : d94569 q = 1) (hb : d116753 q = 1) : d121382 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94569, d121382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94569, d121382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94570 q = 1) (hb : d116753 q = 1) : d121383 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94570, d121383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94570, d121383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94571 q = 1) (hb : d116753 q = 1) : d121384 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94571, d121384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94571, d121384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94572 q = 1) (hb : d116753 q = 1) : d121385 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94572, d121385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94572, d121385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94573 q = 1) (hb : d116753 q = 1) : d121386 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94573, d121386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94573, d121386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20387 (p : Pattern) (ha : d94577 p = 1) (hb : d116753 p = 1) : d121390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8592 q = 1) (hb : d116753 q = 1) : d120427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19879 q ha hb
    | true =>
      simp only [d8592, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19867 q ha hb
  have h2 (q : Pattern) (ha : d8593 q = 1) (hb : d116753 q = 1) : d120428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8594 q = 1) (hb : d116753 q = 1) : d120429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8594, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8595 q = 1) (hb : d116753 q = 1) : d120430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8596 q = 1) (hb : d116753 q = 1) : d120431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94577 q = 1) (hb : d116753 q = 1) : d121390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94577, d121390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94577, d121390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20388 (p : Pattern) (ha : d94586 p = 1) (hb : d116753 p = 1) : d121399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d116753 q = 1) : d120578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19911 q ha hb
    | true =>
      simp only [d8716, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d116753 q = 1) : d120579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d116753 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19872 q ha hb
    | true =>
      simp only [d1006, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d116753 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94583 q = 1) (hb : d116753 q = 1) : d121396 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94583, d121396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94583, d121396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94584 q = 1) (hb : d116753 q = 1) : d121397 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94584, d121397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94584, d121397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94585 q = 1) (hb : d116753 q = 1) : d121398 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94585, d121398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94585, d121398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94586 q = 1) (hb : d116753 q = 1) : d121399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94586, d121399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94586, d121399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20389 (p : Pattern) (ha : d94592 p = 1) (hb : d116753 p = 1) : d121405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94587 q = 1) (hb : d116753 q = 1) : d121400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94587, d121400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20388 q ha hb
    | true =>
      simp only [d94587, d121400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19873 q ha hb
  have h2 (q : Pattern) (ha : d94588 q = 1) (hb : d116753 q = 1) : d121401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94588, d121401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94588, d121401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94589 q = 1) (hb : d116753 q = 1) : d121402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94589, d121402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94589, d121402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94590 q = 1) (hb : d116753 q = 1) : d121403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94590, d121403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94590, d121403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94591 q = 1) (hb : d116753 q = 1) : d121404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94591, d121404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94591, d121404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94592 q = 1) (hb : d116753 q = 1) : d121405 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94592, d121405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94592, d121405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20390 (p : Pattern) (ha : d94598 p = 1) (hb : d116753 p = 1) : d121411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d116753 q = 1) : d120433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19878 q ha hb
    | true =>
      simp only [d8598, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19880 q ha hb
  have h2 (q : Pattern) (ha : d8599 q = 1) (hb : d116753 q = 1) : d120434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94575 q = 1) (hb : d116753 q = 1) : d121388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94575, d121388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94575, d121388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94576 q = 1) (hb : d116753 q = 1) : d121389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94576, d121389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94576, d121389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94578 q = 1) (hb : d116753 q = 1) : d121391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94578, d121391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94578, d121391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20387 q ha hb
  have h6 (q : Pattern) (ha : d94579 q = 1) (hb : d116753 q = 1) : d121392 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94579, d121392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94579, d121392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94580 q = 1) (hb : d116753 q = 1) : d121393 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94580, d121393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94580, d121393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94581 q = 1) (hb : d116753 q = 1) : d121394 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94581, d121394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94581, d121394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94582 q = 1) (hb : d116753 q = 1) : d121395 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94582, d121395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94582, d121395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94593 q = 1) (hb : d116753 q = 1) : d121406 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94593, d121406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94593, d121406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20389 q ha hb
  have h11 (q : Pattern) (ha : d94594 q = 1) (hb : d116753 q = 1) : d121407 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94594, d121407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94594, d121407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94595 q = 1) (hb : d116753 q = 1) : d121408 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94595, d121408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94595, d121408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94596 q = 1) (hb : d116753 q = 1) : d121409 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94596, d121409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94596, d121409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94597 q = 1) (hb : d116753 q = 1) : d121410 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94597, d121410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94597, d121410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94598 q = 1) (hb : d116753 q = 1) : d121411 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94598, d121411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94598, d121411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20391 (p : Pattern) (ha : d94604 p = 1) (hb : d116753 p = 1) : d121417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94599 q = 1) (hb : d116753 q = 1) : d121412 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94599, d121412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94599, d121412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20390 q ha hb
  have h2 (q : Pattern) (ha : d94600 q = 1) (hb : d116753 q = 1) : d121413 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94600, d121413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94600, d121413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94601 q = 1) (hb : d116753 q = 1) : d121414 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94601, d121414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94601, d121414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94602 q = 1) (hb : d116753 q = 1) : d121415 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94602, d121415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94602, d121415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94603 q = 1) (hb : d116753 q = 1) : d121416 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94603, d121416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94603, d121416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94604 q = 1) (hb : d116753 q = 1) : d121417 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94604, d121417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94604, d121417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20392 (p : Pattern) (ha : d94609 p = 1) (hb : d116753 p = 1) : d121422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8759 q = 1) (hb : d116753 q = 1) : d120652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19934 q ha hb
    | true =>
      simp only [d8759, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19921 q ha hb
  have h2 (q : Pattern) (ha : d8760 q = 1) (hb : d116753 q = 1) : d120653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8761 q = 1) (hb : d116753 q = 1) : d120654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8761, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8762 q = 1) (hb : d116753 q = 1) : d120655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8763 q = 1) (hb : d116753 q = 1) : d120656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94609 q = 1) (hb : d116753 q = 1) : d121422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94609, d121422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94609, d121422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20393 (p : Pattern) (ha : d94618 p = 1) (hb : d116753 p = 1) : d121431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d116753 q = 1) : d120805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19968 q ha hb
    | true =>
      simp only [d8883, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d116753 q = 1) : d120806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d116753 q = 1) : d120795 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19926 q ha hb
    | true =>
      simp only [d1431, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d116753 q = 1) : d120796 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94615 q = 1) (hb : d116753 q = 1) : d121428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94615, d121428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94615, d121428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94616 q = 1) (hb : d116753 q = 1) : d121429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94616, d121429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94616, d121429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94617 q = 1) (hb : d116753 q = 1) : d121430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94617, d121430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94617, d121430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94618 q = 1) (hb : d116753 q = 1) : d121431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94618, d121431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94618, d121431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20394 (p : Pattern) (ha : d94624 p = 1) (hb : d116753 p = 1) : d121437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94619 q = 1) (hb : d116753 q = 1) : d121432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94619, d121432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20393 q ha hb
    | true =>
      simp only [d94619, d121432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19927 q ha hb
  have h2 (q : Pattern) (ha : d94620 q = 1) (hb : d116753 q = 1) : d121433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94620, d121433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94620, d121433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94621 q = 1) (hb : d116753 q = 1) : d121434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94621, d121434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94621, d121434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94622 q = 1) (hb : d116753 q = 1) : d121435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94622, d121435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94622, d121435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94623 q = 1) (hb : d116753 q = 1) : d121436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94623, d121436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94623, d121436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94624 q = 1) (hb : d116753 q = 1) : d121437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94624, d121437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94624, d121437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20395 (p : Pattern) (ha : d94630 p = 1) (hb : d116753 p = 1) : d121443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d116753 q = 1) : d120658 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19933 q ha hb
    | true =>
      simp only [d8765, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19935 q ha hb
  have h2 (q : Pattern) (ha : d8766 q = 1) (hb : d116753 q = 1) : d120659 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94607 q = 1) (hb : d116753 q = 1) : d121420 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94607, d121420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94607, d121420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94608 q = 1) (hb : d116753 q = 1) : d121421 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94608, d121421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94608, d121421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94610 q = 1) (hb : d116753 q = 1) : d121423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94610, d121423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94610, d121423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20392 q ha hb
  have h6 (q : Pattern) (ha : d94611 q = 1) (hb : d116753 q = 1) : d121424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94611, d121424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94611, d121424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94612 q = 1) (hb : d116753 q = 1) : d121425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94612, d121425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94612, d121425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94613 q = 1) (hb : d116753 q = 1) : d121426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94613, d121426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94613, d121426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94614 q = 1) (hb : d116753 q = 1) : d121427 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94614, d121427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94614, d121427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94625 q = 1) (hb : d116753 q = 1) : d121438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94625, d121438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94625, d121438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20394 q ha hb
  have h11 (q : Pattern) (ha : d94626 q = 1) (hb : d116753 q = 1) : d121439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94626, d121439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94626, d121439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94627 q = 1) (hb : d116753 q = 1) : d121440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94627, d121440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94627, d121440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94628 q = 1) (hb : d116753 q = 1) : d121441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94628, d121441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94628, d121441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94629 q = 1) (hb : d116753 q = 1) : d121442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94629, d121442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94629, d121442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94630 q = 1) (hb : d116753 q = 1) : d121443 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94630, d121443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94630, d121443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20396 (p : Pattern) (ha : d94636 p = 1) (hb : d116753 p = 1) : d121449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94631 q = 1) (hb : d116753 q = 1) : d121444 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94631, d121444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94631, d121444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20395 q ha hb
  have h2 (q : Pattern) (ha : d94632 q = 1) (hb : d116753 q = 1) : d121445 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94632, d121445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94632, d121445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94633 q = 1) (hb : d116753 q = 1) : d121446 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94633, d121446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94633, d121446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94634 q = 1) (hb : d116753 q = 1) : d121447 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94634, d121447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94634, d121447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94635 q = 1) (hb : d116753 q = 1) : d121448 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94635, d121448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94635, d121448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94636 q = 1) (hb : d116753 q = 1) : d121449 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94636, d121449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94636, d121449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20397 (p : Pattern) (ha : d94642 p = 1) (hb : d116753 p = 1) : d121455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8927 q = 1) (hb : d116753 q = 1) : d120880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19991 q ha hb
    | true =>
      simp only [d8927, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19978 q ha hb
  have h2 (q : Pattern) (ha : d8928 q = 1) (hb : d116753 q = 1) : d120881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8929 q = 1) (hb : d116753 q = 1) : d120882 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8929, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8930 q = 1) (hb : d116753 q = 1) : d120883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8931 q = 1) (hb : d116753 q = 1) : d120884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94642 q = 1) (hb : d116753 q = 1) : d121455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94642, d121455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94642, d121455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20398 (p : Pattern) (ha : d94651 p = 1) (hb : d116753 p = 1) : d121464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d116753 q = 1) : d121033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20025 q ha hb
    | true =>
      simp only [d9051, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d116753 q = 1) : d121034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d116753 q = 1) : d121023 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19983 q ha hb
    | true =>
      simp only [d1908, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d116753 q = 1) : d121024 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94648 q = 1) (hb : d116753 q = 1) : d121461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94648, d121461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94648, d121461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94649 q = 1) (hb : d116753 q = 1) : d121462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94649, d121462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94649, d121462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94650 q = 1) (hb : d116753 q = 1) : d121463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94650, d121463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94650, d121463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94651 q = 1) (hb : d116753 q = 1) : d121464 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94651, d121464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94651, d121464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20399 (p : Pattern) (ha : d94657 p = 1) (hb : d116753 p = 1) : d121470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94652 q = 1) (hb : d116753 q = 1) : d121465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94652, d121465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20398 q ha hb
    | true =>
      simp only [d94652, d121465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19984 q ha hb
  have h2 (q : Pattern) (ha : d94653 q = 1) (hb : d116753 q = 1) : d121466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94653, d121466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94653, d121466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94654 q = 1) (hb : d116753 q = 1) : d121467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94654, d121467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94654, d121467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94655 q = 1) (hb : d116753 q = 1) : d121468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94655, d121468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94655, d121468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94656 q = 1) (hb : d116753 q = 1) : d121469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94656, d121469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94656, d121469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94657 q = 1) (hb : d116753 q = 1) : d121470 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94657, d121470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94657, d121470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20400 (p : Pattern) (ha : d94663 p = 1) (hb : d116753 p = 1) : d121476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d116753 q = 1) : d120886 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19990 q ha hb
    | true =>
      simp only [d8933, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19992 q ha hb
  have h2 (q : Pattern) (ha : d8934 q = 1) (hb : d116753 q = 1) : d120887 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94640 q = 1) (hb : d116753 q = 1) : d121453 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94640, d121453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94640, d121453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94641 q = 1) (hb : d116753 q = 1) : d121454 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94641, d121454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94641, d121454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94643 q = 1) (hb : d116753 q = 1) : d121456 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94643, d121456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94643, d121456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20397 q ha hb
  have h6 (q : Pattern) (ha : d94644 q = 1) (hb : d116753 q = 1) : d121457 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94644, d121457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94644, d121457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94645 q = 1) (hb : d116753 q = 1) : d121458 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94645, d121458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94645, d121458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94646 q = 1) (hb : d116753 q = 1) : d121459 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94646, d121459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94646, d121459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94647 q = 1) (hb : d116753 q = 1) : d121460 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94647, d121460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94647, d121460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94658 q = 1) (hb : d116753 q = 1) : d121471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94658, d121471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94658, d121471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20399 q ha hb
  have h11 (q : Pattern) (ha : d94659 q = 1) (hb : d116753 q = 1) : d121472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94659, d121472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94659, d121472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94660 q = 1) (hb : d116753 q = 1) : d121473 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94660, d121473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94660, d121473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94661 q = 1) (hb : d116753 q = 1) : d121474 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94661, d121474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94661, d121474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94662 q = 1) (hb : d116753 q = 1) : d121475 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94662, d121475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94662, d121475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94663 q = 1) (hb : d116753 q = 1) : d121476 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94663, d121476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94663, d121476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20401 (p : Pattern) (ha : d94669 p = 1) (hb : d116753 p = 1) : d121482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94664 q = 1) (hb : d116753 q = 1) : d121477 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94664, d121477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94664, d121477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20400 q ha hb
  have h2 (q : Pattern) (ha : d94665 q = 1) (hb : d116753 q = 1) : d121478 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94665, d121478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94665, d121478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94666 q = 1) (hb : d116753 q = 1) : d121479 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94666, d121479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94666, d121479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94667 q = 1) (hb : d116753 q = 1) : d121480 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94667, d121480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94667, d121480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94668 q = 1) (hb : d116753 q = 1) : d121481 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94668, d121481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94668, d121481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94669 q = 1) (hb : d116753 q = 1) : d121482 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94669, d121482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94669, d121482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20402 (p : Pattern) (ha : d94676 p = 1) (hb : d116753 p = 1) : d121489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9096 q = 1) (hb : d116753 q = 1) : d121109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20048 q ha hb
    | true =>
      simp only [d9096, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20035 q ha hb
  have h2 (q : Pattern) (ha : d9097 q = 1) (hb : d116753 q = 1) : d121110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9098 q = 1) (hb : d116753 q = 1) : d121111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9098, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9099 q = 1) (hb : d116753 q = 1) : d121112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9100 q = 1) (hb : d116753 q = 1) : d121113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94676 q = 1) (hb : d116753 q = 1) : d121489 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94676, d121489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94676, d121489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20403 (p : Pattern) (ha : d94685 p = 1) (hb : d116753 p = 1) : d121498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d116753 q = 1) : d121262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20082 q ha hb
    | true =>
      simp only [d9220, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d116753 q = 1) : d121263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d116753 q = 1) : d121252 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20040 q ha hb
    | true =>
      simp only [d2386, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d116753 q = 1) : d121253 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94682 q = 1) (hb : d116753 q = 1) : d121495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94682, d121495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94682, d121495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94683 q = 1) (hb : d116753 q = 1) : d121496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94683, d121496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94683, d121496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94684 q = 1) (hb : d116753 q = 1) : d121497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94684, d121497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94684, d121497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94685 q = 1) (hb : d116753 q = 1) : d121498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94685, d121498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94685, d121498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20404 (p : Pattern) (ha : d94691 p = 1) (hb : d116753 p = 1) : d121504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94686 q = 1) (hb : d116753 q = 1) : d121499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94686, d121499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20403 q ha hb
    | true =>
      simp only [d94686, d121499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20041 q ha hb
  have h2 (q : Pattern) (ha : d94687 q = 1) (hb : d116753 q = 1) : d121500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94687, d121500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94687, d121500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94688 q = 1) (hb : d116753 q = 1) : d121501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94688, d121501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94688, d121501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94689 q = 1) (hb : d116753 q = 1) : d121502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94689, d121502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94689, d121502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94690 q = 1) (hb : d116753 q = 1) : d121503 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94690, d121503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94690, d121503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94691 q = 1) (hb : d116753 q = 1) : d121504 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94691, d121504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94691, d121504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20405 (p : Pattern) (ha : d94697 p = 1) (hb : d116753 p = 1) : d121510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d116753 q = 1) : d121115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20047 q ha hb
    | true =>
      simp only [d9102, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20049 q ha hb
  have h2 (q : Pattern) (ha : d9103 q = 1) (hb : d116753 q = 1) : d121116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94674 q = 1) (hb : d116753 q = 1) : d121487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94674, d121487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94674, d121487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94675 q = 1) (hb : d116753 q = 1) : d121488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94675, d121488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94675, d121488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94677 q = 1) (hb : d116753 q = 1) : d121490 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94677, d121490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94677, d121490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20402 q ha hb
  have h6 (q : Pattern) (ha : d94678 q = 1) (hb : d116753 q = 1) : d121491 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94678, d121491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94678, d121491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d94679 q = 1) (hb : d116753 q = 1) : d121492 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94679, d121492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94679, d121492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94680 q = 1) (hb : d116753 q = 1) : d121493 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94680, d121493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94680, d121493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d94681 q = 1) (hb : d116753 q = 1) : d121494 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94681, d121494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94681, d121494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94692 q = 1) (hb : d116753 q = 1) : d121505 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94692, d121505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94692, d121505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20404 q ha hb
  have h11 (q : Pattern) (ha : d94693 q = 1) (hb : d116753 q = 1) : d121506 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94693, d121506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94693, d121506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94694 q = 1) (hb : d116753 q = 1) : d121507 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94694, d121507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94694, d121507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94695 q = 1) (hb : d116753 q = 1) : d121508 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94695, d121508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94695, d121508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94696 q = 1) (hb : d116753 q = 1) : d121509 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94696, d121509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94696, d121509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94697 q = 1) (hb : d116753 q = 1) : d121510 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94697, d121510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94697, d121510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20406 (p : Pattern) (ha : d94703 p = 1) (hb : d116753 p = 1) : d121516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94698 q = 1) (hb : d116753 q = 1) : d121511 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94698, d121511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94698, d121511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20405 q ha hb
  have h2 (q : Pattern) (ha : d94699 q = 1) (hb : d116753 q = 1) : d121512 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94699, d121512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94699, d121512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94700 q = 1) (hb : d116753 q = 1) : d121513 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94700, d121513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94700, d121513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94701 q = 1) (hb : d116753 q = 1) : d121514 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94701, d121514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94701, d121514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94702 q = 1) (hb : d116753 q = 1) : d121515 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94702, d121515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94702, d121515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94703 q = 1) (hb : d116753 q = 1) : d121516 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94703, d121516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94703, d121516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20407 (p : Pattern) (ha : d94709 p = 1) (hb : d116753 p = 1) : d121522 p = 1 := by
  have h0 (q : Pattern) (ha : d94574 q = 1) (hb : d116753 q = 1) : d121387 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94574, d121387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20381 q ha hb
    | true =>
      simp only [d94574, d121387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20386 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94605 q = 1) (hb : d116753 q = 1) : d121418 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94605, d121418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94605, d121418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20391 q ha hb
  have h3 (q : Pattern) (ha : d94606 q = 1) (hb : d116753 q = 1) : d121419 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94606, d121419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94606, d121419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94637 q = 1) (hb : d116753 q = 1) : d121450 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94637, d121450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94637, d121450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20396 q ha hb
  have h5 (q : Pattern) (ha : d94638 q = 1) (hb : d116753 q = 1) : d121451 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94638, d121451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94638, d121451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94639 q = 1) (hb : d116753 q = 1) : d121452 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94639, d121452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94639, d121452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94670 q = 1) (hb : d116753 q = 1) : d121483 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94670, d121483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94670, d121483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20401 q ha hb
  have h8 (q : Pattern) (ha : d94671 q = 1) (hb : d116753 q = 1) : d121484 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94671, d121484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94671, d121484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94672 q = 1) (hb : d116753 q = 1) : d121485 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94672, d121485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94672, d121485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94673 q = 1) (hb : d116753 q = 1) : d121486 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94673, d121486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94673, d121486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94704 q = 1) (hb : d116753 q = 1) : d121517 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94704, d121517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94704, d121517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20406 q ha hb
  have h12 (q : Pattern) (ha : d94705 q = 1) (hb : d116753 q = 1) : d121518 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94705, d121518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94705, d121518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94706 q = 1) (hb : d116753 q = 1) : d121519 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94706, d121519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94706, d121519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94707 q = 1) (hb : d116753 q = 1) : d121520 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94707, d121520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94707, d121520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94708 q = 1) (hb : d116753 q = 1) : d121521 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94708, d121521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94708, d121521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94709 q = 1) (hb : d116753 q = 1) : d121522 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94709, d121522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94709, d121522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro20408 (p : Pattern) (ha : d94715 p = 1) (hb : d116753 p = 1) : d121528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94710 q = 1) (hb : d116753 q = 1) : d121523 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94710, d121523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20407 q ha hb
    | true =>
      simp only [d94710, d121523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94711 q = 1) (hb : d116753 q = 1) : d121524 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94711, d121524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94711, d121524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94712 q = 1) (hb : d116753 q = 1) : d121525 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94712, d121525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94712, d121525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94713 q = 1) (hb : d116753 q = 1) : d121526 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94713, d121526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94713, d121526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94714 q = 1) (hb : d116753 q = 1) : d121527 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94714, d121527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94714, d121527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94715 q = 1) (hb : d116753 q = 1) : d121528 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94715, d121528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94715, d121528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20409 (p : Pattern) (ha : d94721 p = 1) (hb : d116753 p = 1) : d121534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94716 q = 1) (hb : d116753 q = 1) : d121529 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94716, d121529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20408 q ha hb
    | true =>
      simp only [d94716, d121529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94717 q = 1) (hb : d116753 q = 1) : d121530 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94717, d121530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94717, d121530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94718 q = 1) (hb : d116753 q = 1) : d121531 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94718, d121531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94718, d121531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94719 q = 1) (hb : d116753 q = 1) : d121532 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94719, d121532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94719, d121532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94720 q = 1) (hb : d116753 q = 1) : d121533 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94720, d121533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94720, d121533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94721 q = 1) (hb : d116753 q = 1) : d121534 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94721, d121534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94721, d121534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20410 (p : Pattern) (ha : d94727 p = 1) (hb : d116753 p = 1) : d121540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94722 q = 1) (hb : d116753 q = 1) : d121535 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94722, d121535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20409 q ha hb
    | true =>
      simp only [d94722, d121535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94723 q = 1) (hb : d116753 q = 1) : d121536 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94723, d121536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94723, d121536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94724 q = 1) (hb : d116753 q = 1) : d121537 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94724, d121537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94724, d121537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94725 q = 1) (hb : d116753 q = 1) : d121538 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94725, d121538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94725, d121538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94726 q = 1) (hb : d116753 q = 1) : d121539 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94726, d121539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94726, d121539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94727 q = 1) (hb : d116753 q = 1) : d121540 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94727, d121540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94727, d121540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20411 (p : Pattern) (ha : d94733 p = 1) (hb : d116753 p = 1) : d121546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94728 q = 1) (hb : d116753 q = 1) : d121541 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94728, d121541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20410 q ha hb
    | true =>
      simp only [d94728, d121541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94729 q = 1) (hb : d116753 q = 1) : d121542 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94729, d121542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94729, d121542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94730 q = 1) (hb : d116753 q = 1) : d121543 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94730, d121543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94730, d121543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94731 q = 1) (hb : d116753 q = 1) : d121544 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94731, d121544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94731, d121544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94732 q = 1) (hb : d116753 q = 1) : d121545 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94732, d121545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94732, d121545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94733 q = 1) (hb : d116753 q = 1) : d121546 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94733, d121546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94733, d121546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20412 (p : Pattern) (ha : d94739 p = 1) (hb : d116753 p = 1) : d121552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94734 q = 1) (hb : d116753 q = 1) : d121547 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94734, d121547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20411 q ha hb
    | true =>
      simp only [d94734, d121547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94735 q = 1) (hb : d116753 q = 1) : d121548 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94735, d121548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94735, d121548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94736 q = 1) (hb : d116753 q = 1) : d121549 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94736, d121549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94736, d121549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94737 q = 1) (hb : d116753 q = 1) : d121550 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94737, d121550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94737, d121550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94738 q = 1) (hb : d116753 q = 1) : d121551 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94738, d121551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94738, d121551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94739 q = 1) (hb : d116753 q = 1) : d121552 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94739, d121552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94739, d121552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20413 (p : Pattern) (ha : d94745 p = 1) (hb : d116753 p = 1) : d121558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94740 q = 1) (hb : d116753 q = 1) : d121553 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94740, d121553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20412 q ha hb
    | true =>
      simp only [d94740, d121553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94741 q = 1) (hb : d116753 q = 1) : d121554 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94741, d121554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94741, d121554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94742 q = 1) (hb : d116753 q = 1) : d121555 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94742, d121555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94742, d121555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94743 q = 1) (hb : d116753 q = 1) : d121556 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94743, d121556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94743, d121556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94744 q = 1) (hb : d116753 q = 1) : d121557 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94744, d121557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94744, d121557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94745 q = 1) (hb : d116753 q = 1) : d121558 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94745, d121558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94745, d121558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20414 (p : Pattern) (ha : d94751 p = 1) (hb : d116753 p = 1) : d121564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94746 q = 1) (hb : d116753 q = 1) : d121559 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94746, d121559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20413 q ha hb
    | true =>
      simp only [d94746, d121559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94747 q = 1) (hb : d116753 q = 1) : d121560 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94747, d121560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94747, d121560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94748 q = 1) (hb : d116753 q = 1) : d121561 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94748, d121561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94748, d121561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94749 q = 1) (hb : d116753 q = 1) : d121562 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94749, d121562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94749, d121562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94750 q = 1) (hb : d116753 q = 1) : d121563 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94750, d121563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94750, d121563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94751 q = 1) (hb : d116753 q = 1) : d121564 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94751, d121564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94751, d121564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20415 (p : Pattern) (ha : d118738 p = 1) (hb : d120136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118709 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118715 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d118733 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118734 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118734, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d118734, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118633 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118735 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118735, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118735, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118736 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118736, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d118736, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118737 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118737, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118737, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118738 q = 1) (hb : d120136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118738, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118738, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20416 (p : Pattern) (ha : d118754 p = 1) (hb : d120143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118709 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118733 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d118632 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
    | true =>
      simp only [d118632, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d118734 q = 1) (hb : d120132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118734, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d118734, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118633 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118735 q = 1) (hb : d120133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118735, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118735, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118736 q = 1) (hb : d120134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118736, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118736, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118737 q = 1) (hb : d120135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118737, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118737, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d118743 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d118747 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d118749 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d118750 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118750, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d118750, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d118640 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d118751 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118751, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d118751, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d118752 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118752, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d118752, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d118753 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118753, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d118753, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d118754 q = 1) (hb : d120143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118754, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d118754, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20417 (p : Pattern) (ha : d118763 p = 1) (hb : d120334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118749 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118639 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
    | true =>
      simp only [d118639, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118750 q = 1) (hb : d120139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118750, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118750, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118640 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118751 q = 1) (hb : d120140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118751, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118751, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118761 q = 1) (hb : d120141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118761, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118761, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118762 q = 1) (hb : d120142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118762, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118762, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118763 q = 1) (hb : d120334 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118763, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118763, d120334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20418 (p : Pattern) (ha : d118791 p = 1) (hb : d120378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118786 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118672 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20105 q ha hb
    | true =>
      simp only [d118672, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118787 q = 1) (hb : d120374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118787, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118787, d120374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118788 q = 1) (hb : d120375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118788, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118788, d120375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118789 q = 1) (hb : d120376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118789, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118789, d120376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118790 q = 1) (hb : d120377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118790, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118790, d120377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118791 q = 1) (hb : d120378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118791, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118791, d120378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20419 (p : Pattern) (ha : d118797 p = 1) (hb : d121355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118703 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118755 q = 1) (hb : d120144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118755, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20415 q ha hb
    | true =>
      simp only [d118755, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20416 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118758 q = 1) (hb : d120145 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118758, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118758, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118759 q = 1) (hb : d121345 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118759, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118759, d121345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118760 q = 1) (hb : d121346 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118760, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118760, d121346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118764 q = 1) (hb : d120335 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118764, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d118764, d120335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20417 q ha hb
  have h8 (q : Pattern) (ha : d118765 q = 1) (hb : d121347 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118765, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118765, d121347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d118766 q = 1) (hb : d121348 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118766, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118766, d121348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d118767 q = 1) (hb : d121349 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118767, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d118767, d121349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d118768 q = 1) (hb : d121350 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118768, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118768, d121350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d118792 q = 1) (hb : d120379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118792, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d118792, d120379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20418 q ha hb
  have h13 (q : Pattern) (ha : d118793 q = 1) (hb : d121351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118793, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d118793, d121351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d118794 q = 1) (hb : d121352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118794, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d118794, d121352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d118795 q = 1) (hb : d121353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118795, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d118795, d121353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d118796 q = 1) (hb : d121354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118796, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d118796, d121354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d118797 q = 1) (hb : d121355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118797, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118797, d121355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20420 (p : Pattern) (ha : d118803 p = 1) (hb : d121361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118798 q = 1) (hb : d121356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118798, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118798, d121356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20419 q ha hb
  have h3 (q : Pattern) (ha : d118799 q = 1) (hb : d121357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118799, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118799, d121357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118800 q = 1) (hb : d121358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118800, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118800, d121358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118801 q = 1) (hb : d121359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118801, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118801, d121359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118802 q = 1) (hb : d121360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118802, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118802, d121360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118803 q = 1) (hb : d121361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118803, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118803, d121361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20421 (p : Pattern) (ha : d118859 p = 1) (hb : d120243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118824 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118830 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d118848 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d118733 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20115 q ha hb
    | true =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
  have h5 (q : Pattern) (ha : d118849 q = 1) (hb : d120239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118849, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d118849, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118855 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118856 q = 1) (hb : d120240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118856, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118856, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118857 q = 1) (hb : d120241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118857, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d118857, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d118858 q = 1) (hb : d120242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118858, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118858, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118859 q = 1) (hb : d120243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118859, d120243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118859, d120243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20422 (p : Pattern) (ha : d118878 p = 1) (hb : d120250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118824 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118830 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118848 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118733 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20115 q ha hb
    | true =>
      simp only [d118733, d120172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20098 q ha hb
  have h4 (q : Pattern) (ha : d118849 q = 1) (hb : d120239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118849, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d118849, d120239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d118855 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d118856 q = 1) (hb : d120240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118856, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118856, d120240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d118857 q = 1) (hb : d120241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118857, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118857, d120241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118858 q = 1) (hb : d120242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118858, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118858, d120242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118864 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d118868 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d118870 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d118749 q = 1) (hb : d120188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20119 q ha hb
    | true =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
  have h13 (q : Pattern) (ha : d118871 q = 1) (hb : d120246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118871, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d118871, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d118874 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d118875 q = 1) (hb : d120247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118875, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d118875, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d118876 q = 1) (hb : d120248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118876, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d118876, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d118877 q = 1) (hb : d120249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118877, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d118877, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d118878 q = 1) (hb : d120250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118878, d120250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118878, d120250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20423 (p : Pattern) (ha : d118887 p = 1) (hb : d121364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118870 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118749 q = 1) (hb : d120188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20119 q ha hb
    | true =>
      simp only [d118749, d120188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20100 q ha hb
  have h3 (q : Pattern) (ha : d118871 q = 1) (hb : d120246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118871, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118871, d120246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118874 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118875 q = 1) (hb : d120247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118875, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118875, d120247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118885 q = 1) (hb : d120248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118885, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118885, d120248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118886 q = 1) (hb : d120249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118886, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118886, d120249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118887 q = 1) (hb : d121364 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118887, d121364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118887, d121364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20424 (p : Pattern) (ha : d118923 p = 1) (hb : d121374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118786 q = 1) (hb : d120221 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118786, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20125 q ha hb
    | true =>
      simp only [d118786, d120221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20105 q ha hb
  have h3 (q : Pattern) (ha : d118913 q = 1) (hb : d121370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118913, d121370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d118913, d121370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118919 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118920 q = 1) (hb : d121371 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118920, d121371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118920, d121371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118921 q = 1) (hb : d121372 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118921, d121372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118921, d121372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118922 q = 1) (hb : d121373 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118922, d121373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118922, d121373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118923 q = 1) (hb : d121374 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118923, d121374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118923, d121374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20425 (p : Pattern) (ha : d118935 p = 1) (hb : d121380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118818 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118879 q = 1) (hb : d120251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118879, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20421 q ha hb
    | true =>
      simp only [d118879, d120251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20422 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118882 q = 1) (hb : d120252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118882, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118882, d120252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d118883 q = 1) (hb : d121362 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118883, d121362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118883, d121362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d118884 q = 1) (hb : d121363 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118884, d121363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118884, d121363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d118888 q = 1) (hb : d121365 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118888, d121365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d118888, d121365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20423 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d118890 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d118891 q = 1) (hb : d121366 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118891, d121366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118891, d121366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d118892 q = 1) (hb : d121367 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118892, d121367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d118892, d121367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d118893 q = 1) (hb : d121368 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118893, d121368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d118893, d121368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d118894 q = 1) (hb : d121369 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118894, d121369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118894, d121369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d118924 q = 1) (hb : d121375 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118924, d121375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d118924, d121375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20424 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d118930 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d118931 q = 1) (hb : d121376 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118931, d121376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d118931, d121376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d118932 q = 1) (hb : d121377 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118932, d121377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d118932, d121377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d118933 q = 1) (hb : d121378 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118933, d121378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d118933, d121378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d118934 q = 1) (hb : d121379 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118934, d121379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d118934, d121379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d118935 q = 1) (hb : d121380 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118935, d121380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d118935, d121380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20426 (p : Pattern) (ha : d118941 p = 1) (hb : d121386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118936 q = 1) (hb : d121381 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118936, d121381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118936, d121381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20425 q ha hb
  have h2 (q : Pattern) (ha : d118937 q = 1) (hb : d121382 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118937, d121382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118937, d121382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118938 q = 1) (hb : d121383 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118938, d121383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118938, d121383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118939 q = 1) (hb : d121384 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118939, d121384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118939, d121384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118940 q = 1) (hb : d121385 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118940, d121385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118940, d121385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118941 q = 1) (hb : d121386 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118941, d121386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118941, d121386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20427 (p : Pattern) (ha : d119040 p = 1) (hb : d120422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119003 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d119029 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d118968 q = 1) (hb : d120417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20163 q ha hb
    | true =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20164 q ha hb
  have h5 (q : Pattern) (ha : d119030 q = 1) (hb : d120418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119030, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d119030, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119036 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119037 q = 1) (hb : d120419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119037, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119037, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119038 q = 1) (hb : d120420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119038, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119038, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119039 q = 1) (hb : d120421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119039, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119039, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119040 q = 1) (hb : d120422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119040, d120422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119040, d120422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20428 (p : Pattern) (ha : d119061 p = 1) (hb : d120432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118994 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119003 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119029 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118968 q = 1) (hb : d120417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20163 q ha hb
    | true =>
      simp only [d118968, d120417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20164 q ha hb
  have h4 (q : Pattern) (ha : d119030 q = 1) (hb : d120418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119030, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119030, d120418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d119036 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d119037 q = 1) (hb : d120419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119037, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119037, d120419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d119038 q = 1) (hb : d120420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119038, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119038, d120420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119039 q = 1) (hb : d120421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119039, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119039, d120421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119046 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d119051 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d119053 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d118978 q = 1) (hb : d120427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118978, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20166 q ha hb
    | true =>
      simp only [d118978, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20167 q ha hb
  have h13 (q : Pattern) (ha : d119054 q = 1) (hb : d120428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119054, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d119054, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119057 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d119058 q = 1) (hb : d120429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119058, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119058, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d119059 q = 1) (hb : d120430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119059, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d119059, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119060 q = 1) (hb : d120431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119060, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d119060, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119061 q = 1) (hb : d120432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119061, d120432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119061, d120432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20429 (p : Pattern) (ha : d119081 p = 1) (hb : d121390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119053 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118978 q = 1) (hb : d120427 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118978, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20166 q ha hb
    | true =>
      simp only [d118978, d120427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20167 q ha hb
  have h3 (q : Pattern) (ha : d119054 q = 1) (hb : d120428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119054, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119054, d120428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119057 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119058 q = 1) (hb : d120429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119058, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119058, d120429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119079 q = 1) (hb : d120430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119079, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119079, d120430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119080 q = 1) (hb : d120431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119080, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119080, d120431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119081 q = 1) (hb : d121390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119081, d121390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119081, d121390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20430 (p : Pattern) (ha : d119134 p = 1) (hb : d121399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119121 q = 1) (hb : d120578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119121, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20200 q ha hb
    | true =>
      simp only [d119121, d120578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119122 q = 1) (hb : d120579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119122, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119122, d120579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119129 q = 1) (hb : d120568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119129, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20198 q ha hb
    | true =>
      simp only [d119129, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119130 q = 1) (hb : d120569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119130, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119130, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119131 q = 1) (hb : d121396 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119131, d121396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119131, d121396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119132 q = 1) (hb : d121397 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119132, d121397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119132, d121397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119133 q = 1) (hb : d121398 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119133, d121398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119133, d121398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119134 q = 1) (hb : d121399 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119134, d121399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119134, d121399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20431 (p : Pattern) (ha : d119151 p = 1) (hb : d121405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119140 q = 1) (hb : d121400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119140, d121400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20430 q ha hb
    | true =>
      simp only [d119140, d121400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20203 q ha hb
  have h3 (q : Pattern) (ha : d119141 q = 1) (hb : d121401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119141, d121401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119141, d121401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119148 q = 1) (hb : d121402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119148, d121402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119148, d121402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119149 q = 1) (hb : d121403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119149, d121403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119149, d121403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119150 q = 1) (hb : d121404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119150, d121404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119150, d121404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119151 q = 1) (hb : d121405 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119151, d121405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119151, d121405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20432 (p : Pattern) (ha : d119164 p = 1) (hb : d121411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119062 q = 1) (hb : d120433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119062, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20427 q ha hb
    | true =>
      simp only [d119062, d120433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20428 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119076 q = 1) (hb : d120434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119076, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119076, d120434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119077 q = 1) (hb : d121388 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119077, d121388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119077, d121388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119078 q = 1) (hb : d121389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119078, d121389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119078, d121389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119082 q = 1) (hb : d121391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119082, d121391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119082, d121391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20429 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119084 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d119085 q = 1) (hb : d121392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119085, d121392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119085, d121392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d119086 q = 1) (hb : d121393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119086, d121393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d119086, d121393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d119087 q = 1) (hb : d121394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119087, d121394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119087, d121394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d119088 q = 1) (hb : d121395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119088, d121395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119088, d121395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d119152 q = 1) (hb : d121406 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119152, d121406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119152, d121406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20431 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119159 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d119160 q = 1) (hb : d121407 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119160, d121407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119160, d121407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d119161 q = 1) (hb : d121408 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119161, d121408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d119161, d121408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d119162 q = 1) (hb : d121409 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119162, d121409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d119162, d121409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d119163 q = 1) (hb : d121410 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119163, d121410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119163, d121410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d119164 q = 1) (hb : d121411 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d119164, d121411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d119164, d121411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20433 (p : Pattern) (ha : d119170 p = 1) (hb : d121417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119165 q = 1) (hb : d121412 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d119165, d121412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119165, d121412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20432 q ha hb
  have h2 (q : Pattern) (ha : d119166 q = 1) (hb : d121413 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d119166, d121413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119166, d121413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119167 q = 1) (hb : d121414 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d119167, d121414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119167, d121414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119168 q = 1) (hb : d121415 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d119168, d121415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119168, d121415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119169 q = 1) (hb : d121416 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d119169, d121416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119169, d121416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119170 q = 1) (hb : d121417 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d119170, d121417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119170, d121417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20434 (p : Pattern) (ha : d119284 p = 1) (hb : d120647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119238 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119247 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d119273 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d119212 q = 1) (hb : d120642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20215 q ha hb
    | true =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20216 q ha hb
  have h5 (q : Pattern) (ha : d119274 q = 1) (hb : d120643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119274, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d119274, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119280 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119281 q = 1) (hb : d120644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119281, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119281, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119282 q = 1) (hb : d120645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119282, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119282, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119283 q = 1) (hb : d120646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119283, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119283, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119284 q = 1) (hb : d120647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119284, d120647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119284, d120647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20435 (p : Pattern) (ha : d119305 p = 1) (hb : d120657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119238 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119273 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119212 q = 1) (hb : d120642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20215 q ha hb
    | true =>
      simp only [d119212, d120642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20216 q ha hb
  have h4 (q : Pattern) (ha : d119274 q = 1) (hb : d120643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119274, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119274, d120643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d119280 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d119281 q = 1) (hb : d120644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119281, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119281, d120644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d119282 q = 1) (hb : d120645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119282, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119282, d120645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119283 q = 1) (hb : d120646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119283, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119283, d120646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119290 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d119295 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d119297 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d119222 q = 1) (hb : d120652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119222, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20218 q ha hb
    | true =>
      simp only [d119222, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20219 q ha hb
  have h13 (q : Pattern) (ha : d119298 q = 1) (hb : d120653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119298, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d119298, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119301 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d119302 q = 1) (hb : d120654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119302, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119302, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d119303 q = 1) (hb : d120655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119303, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d119303, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119304 q = 1) (hb : d120656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119304, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d119304, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119305 q = 1) (hb : d120657 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119305, d120657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119305, d120657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20436 (p : Pattern) (ha : d119325 p = 1) (hb : d121422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119222 q = 1) (hb : d120652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119222, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20218 q ha hb
    | true =>
      simp only [d119222, d120652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20219 q ha hb
  have h3 (q : Pattern) (ha : d119298 q = 1) (hb : d120653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119298, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119298, d120653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119301 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119302 q = 1) (hb : d120654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119302, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119302, d120654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119323 q = 1) (hb : d120655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119323, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119323, d120655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119324 q = 1) (hb : d120656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119324, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119324, d120656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119325 q = 1) (hb : d121422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119325, d121422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119325, d121422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20437 (p : Pattern) (ha : d119392 p = 1) (hb : d121431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119379 q = 1) (hb : d120805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119379, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20254 q ha hb
    | true =>
      simp only [d119379, d120805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119380 q = 1) (hb : d120806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119380, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119380, d120806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119387 q = 1) (hb : d120795 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119387, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20252 q ha hb
    | true =>
      simp only [d119387, d120795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119388 q = 1) (hb : d120796 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119388, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119388, d120796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119389 q = 1) (hb : d121428 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119389, d121428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119389, d121428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119390 q = 1) (hb : d121429 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119390, d121429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119390, d121429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119391 q = 1) (hb : d121430 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119391, d121430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119391, d121430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119392 q = 1) (hb : d121431 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119392, d121431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119392, d121431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20438 (p : Pattern) (ha : d119409 p = 1) (hb : d121437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119398 q = 1) (hb : d121432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119398, d121432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20437 q ha hb
    | true =>
      simp only [d119398, d121432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20257 q ha hb
  have h3 (q : Pattern) (ha : d119399 q = 1) (hb : d121433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119399, d121433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119399, d121433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119405 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119406 q = 1) (hb : d121434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119406, d121434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119406, d121434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119407 q = 1) (hb : d121435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119407, d121435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119407, d121435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119408 q = 1) (hb : d121436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119408, d121436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119408, d121436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119409 q = 1) (hb : d121437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119409, d121437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119409, d121437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20439 (p : Pattern) (ha : d119422 p = 1) (hb : d121443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119230 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119306 q = 1) (hb : d120658 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119306, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20434 q ha hb
    | true =>
      simp only [d119306, d120658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20435 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119319 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119320 q = 1) (hb : d120659 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119320, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119320, d120659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119321 q = 1) (hb : d121420 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119321, d121420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119321, d121420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119322 q = 1) (hb : d121421 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119322, d121421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119322, d121421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119326 q = 1) (hb : d121423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119326, d121423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119326, d121423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20436 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119328 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d119329 q = 1) (hb : d121424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119329, d121424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119329, d121424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d119330 q = 1) (hb : d121425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119330, d121425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d119330, d121425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d119331 q = 1) (hb : d121426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119331, d121426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119331, d121426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d119332 q = 1) (hb : d121427 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119332, d121427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119332, d121427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d119410 q = 1) (hb : d121438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119410, d121438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119410, d121438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20438 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119417 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d119418 q = 1) (hb : d121439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119418, d121439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119418, d121439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d119419 q = 1) (hb : d121440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119419, d121440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d119419, d121440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d119420 q = 1) (hb : d121441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119420, d121441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d119420, d121441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d119421 q = 1) (hb : d121442 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119421, d121442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119421, d121442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d119422 q = 1) (hb : d121443 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d119422, d121443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d119422, d121443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20440 (p : Pattern) (ha : d119428 p = 1) (hb : d121449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119423 q = 1) (hb : d121444 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d119423, d121444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119423, d121444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20439 q ha hb
  have h2 (q : Pattern) (ha : d119424 q = 1) (hb : d121445 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d119424, d121445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119424, d121445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119425 q = 1) (hb : d121446 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d119425, d121446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119425, d121446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119426 q = 1) (hb : d121447 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d119426, d121447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119426, d121447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119427 q = 1) (hb : d121448 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d119427, d121448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119427, d121448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119428 q = 1) (hb : d121449 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d119428, d121449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119428, d121449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20441 (p : Pattern) (ha : d119560 p = 1) (hb : d120875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d119549 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d119479 q = 1) (hb : d120870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20269 q ha hb
    | true =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20270 q ha hb
  have h5 (q : Pattern) (ha : d119550 q = 1) (hb : d120871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119550, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d119550, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119557 q = 1) (hb : d120872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119557, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119557, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119558 q = 1) (hb : d120873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119558, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119558, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119559 q = 1) (hb : d120874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119559, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119559, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119560 q = 1) (hb : d120875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119560, d120875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119560, d120875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20442 (p : Pattern) (ha : d119582 p = 1) (hb : d120885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119505 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119479 q = 1) (hb : d120870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20269 q ha hb
    | true =>
      simp only [d119479, d120870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20270 q ha hb
  have h4 (q : Pattern) (ha : d119550 q = 1) (hb : d120871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119550, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119550, d120871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d119556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d119557 q = 1) (hb : d120872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119557, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119557, d120872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d119558 q = 1) (hb : d120873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119558, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119558, d120873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119559 q = 1) (hb : d120874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119559, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119559, d120874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119566 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d119571 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d119574 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d119489 q = 1) (hb : d120880 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119489, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20272 q ha hb
    | true =>
      simp only [d119489, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20273 q ha hb
  have h13 (q : Pattern) (ha : d119575 q = 1) (hb : d120881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119575, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d119575, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119578 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d119579 q = 1) (hb : d120882 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119579, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119579, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d119580 q = 1) (hb : d120883 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119580, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d119580, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119581 q = 1) (hb : d120884 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119581, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d119581, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119582 q = 1) (hb : d120885 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119582, d120885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119582, d120885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20443 (p : Pattern) (ha : d119607 p = 1) (hb : d121455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119489 q = 1) (hb : d120880 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119489, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20272 q ha hb
    | true =>
      simp only [d119489, d120880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20273 q ha hb
  have h3 (q : Pattern) (ha : d119575 q = 1) (hb : d120881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119575, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119575, d120881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119578 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119579 q = 1) (hb : d120882 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119579, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119579, d120882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119605 q = 1) (hb : d120883 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119605, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119605, d120883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119606 q = 1) (hb : d120884 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119606, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119606, d120884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119607 q = 1) (hb : d121455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119607, d121455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119607, d121455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20444 (p : Pattern) (ha : d119692 p = 1) (hb : d121464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119687 q = 1) (hb : d121033 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119687, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20308 q ha hb
    | true =>
      simp only [d119687, d121033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119688 q = 1) (hb : d121034 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119688, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119688, d121034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119678 q = 1) (hb : d121023 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119678, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20306 q ha hb
    | true =>
      simp only [d119678, d121023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119679 q = 1) (hb : d121024 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119679, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119679, d121024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119689 q = 1) (hb : d121461 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119689, d121461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119689, d121461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119690 q = 1) (hb : d121462 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119690, d121462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119690, d121462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119691 q = 1) (hb : d121463 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119691, d121463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119691, d121463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119692 q = 1) (hb : d121464 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119692, d121464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119692, d121464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20445 (p : Pattern) (ha : d119708 p = 1) (hb : d121470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119697 q = 1) (hb : d121465 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119697, d121465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20444 q ha hb
    | true =>
      simp only [d119697, d121465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20311 q ha hb
  have h3 (q : Pattern) (ha : d119698 q = 1) (hb : d121466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119698, d121466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119698, d121466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119704 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119705 q = 1) (hb : d121467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119705, d121467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119705, d121467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119706 q = 1) (hb : d121468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119706, d121468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119706, d121468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119707 q = 1) (hb : d121469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119707, d121469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119707, d121469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119708 q = 1) (hb : d121470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119708, d121470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119708, d121470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20446 (p : Pattern) (ha : d119721 p = 1) (hb : d121476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119497 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119583 q = 1) (hb : d120886 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119583, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20441 q ha hb
    | true =>
      simp only [d119583, d120886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20442 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119601 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119602 q = 1) (hb : d120887 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119602, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119602, d120887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119603 q = 1) (hb : d121453 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119603, d121453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119603, d121453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119604 q = 1) (hb : d121454 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119604, d121454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119604, d121454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119608 q = 1) (hb : d121456 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119608, d121456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119608, d121456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20443 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119610 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d119611 q = 1) (hb : d121457 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119611, d121457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119611, d121457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d119612 q = 1) (hb : d121458 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119612, d121458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d119612, d121458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d119613 q = 1) (hb : d121459 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119613, d121459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119613, d121459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d119614 q = 1) (hb : d121460 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119614, d121460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119614, d121460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d119709 q = 1) (hb : d121471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119709, d121471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119709, d121471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20445 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119716 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d119717 q = 1) (hb : d121472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119717, d121472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119717, d121472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d119718 q = 1) (hb : d121473 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119718, d121473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d119718, d121473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d119719 q = 1) (hb : d121474 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119719, d121474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d119719, d121474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d119720 q = 1) (hb : d121475 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119720, d121475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d119720, d121475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d119721 q = 1) (hb : d121476 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d119721, d121476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d119721, d121476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20447 (p : Pattern) (ha : d119727 p = 1) (hb : d121482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119722 q = 1) (hb : d121477 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d119722, d121477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119722, d121477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20446 q ha hb
  have h2 (q : Pattern) (ha : d119723 q = 1) (hb : d121478 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d119723, d121478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119723, d121478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119724 q = 1) (hb : d121479 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d119724, d121479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119724, d121479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119725 q = 1) (hb : d121480 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d119725, d121480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119725, d121480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119726 q = 1) (hb : d121481 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d119726, d121481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119726, d121481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119727 q = 1) (hb : d121482 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d119727, d121482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119727, d121482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20448 (p : Pattern) (ha : d119855 p = 1) (hb : d121104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119814 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d119844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d119779 q = 1) (hb : d121099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20323 q ha hb
    | true =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20324 q ha hb
  have h5 (q : Pattern) (ha : d119845 q = 1) (hb : d121100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119845, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d119845, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d119851 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d119852 q = 1) (hb : d121101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119852, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119852, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d119853 q = 1) (hb : d121102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119853, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119853, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119854 q = 1) (hb : d121103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119854, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119854, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119855 q = 1) (hb : d121104 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119855, d121104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119855, d121104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20449 (p : Pattern) (ha : d119877 p = 1) (hb : d121114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119805 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119779 q = 1) (hb : d121099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20323 q ha hb
    | true =>
      simp only [d119779, d121099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20324 q ha hb
  have h4 (q : Pattern) (ha : d119845 q = 1) (hb : d121100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119845, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d119845, d121100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d119851 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d119852 q = 1) (hb : d121101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119852, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119852, d121101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d119853 q = 1) (hb : d121102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119853, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119853, d121102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119854 q = 1) (hb : d121103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119854, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119854, d121103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d119861 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d119866 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d119869 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d119789 q = 1) (hb : d121109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119789, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20326 q ha hb
    | true =>
      simp only [d119789, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20327 q ha hb
  have h13 (q : Pattern) (ha : d119870 q = 1) (hb : d121110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119870, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d119870, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119873 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d119874 q = 1) (hb : d121111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119874, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d119874, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d119875 q = 1) (hb : d121112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119875, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d119875, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d119876 q = 1) (hb : d121113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119876, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d119876, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d119877 q = 1) (hb : d121114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119877, d121114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d119877, d121114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20450 (p : Pattern) (ha : d119902 p = 1) (hb : d121489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119789 q = 1) (hb : d121109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119789, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20326 q ha hb
    | true =>
      simp only [d119789, d121109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20327 q ha hb
  have h3 (q : Pattern) (ha : d119870 q = 1) (hb : d121110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119870, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119870, d121110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119873 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119874 q = 1) (hb : d121111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119874, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119874, d121111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119900 q = 1) (hb : d121112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119900, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119900, d121112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119901 q = 1) (hb : d121113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119901, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119901, d121113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119902 q = 1) (hb : d121489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119902, d121489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119902, d121489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20451 (p : Pattern) (ha : d119982 p = 1) (hb : d121498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119977 q = 1) (hb : d121262 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119977, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20362 q ha hb
    | true =>
      simp only [d119977, d121262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119978 q = 1) (hb : d121263 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119978, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119978, d121263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119968 q = 1) (hb : d121252 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119968, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20360 q ha hb
    | true =>
      simp only [d119968, d121252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119969 q = 1) (hb : d121253 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119969, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119969, d121253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119979 q = 1) (hb : d121495 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119979, d121495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119979, d121495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119980 q = 1) (hb : d121496 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119980, d121496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119980, d121496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119981 q = 1) (hb : d121497 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119981, d121497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119981, d121497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d119982 q = 1) (hb : d121498 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119982, d121498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119982, d121498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20452 (p : Pattern) (ha : d119998 p = 1) (hb : d121504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d119974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119987 q = 1) (hb : d121499 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119987, d121499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20451 q ha hb
    | true =>
      simp only [d119987, d121499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20365 q ha hb
  have h3 (q : Pattern) (ha : d119988 q = 1) (hb : d121500 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119988, d121500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119988, d121500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d119994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119995 q = 1) (hb : d121501 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119995, d121501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119995, d121501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119996 q = 1) (hb : d121502 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119996, d121502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119996, d121502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119997 q = 1) (hb : d121503 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119997, d121503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119997, d121503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119998 q = 1) (hb : d121504 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119998, d121504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119998, d121504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20453 (p : Pattern) (ha : d120011 p = 1) (hb : d121510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d119797 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119878 q = 1) (hb : d121115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119878, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20448 q ha hb
    | true =>
      simp only [d119878, d121115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20449 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d119896 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d119897 q = 1) (hb : d121116 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119897, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d119897, d121116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119898 q = 1) (hb : d121487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119898, d121487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119898, d121487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d119899 q = 1) (hb : d121488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119899, d121488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119899, d121488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119903 q = 1) (hb : d121490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119903, d121490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119903, d121490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20450 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119905 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d119906 q = 1) (hb : d121491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d119906, d121491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119906, d121491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d119907 q = 1) (hb : d121492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d119907, d121492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d119907, d121492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d119908 q = 1) (hb : d121493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d119908, d121493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d119908, d121493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d119909 q = 1) (hb : d121494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d119909, d121494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119909, d121494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d119999 q = 1) (hb : d121505 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119999, d121505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d119999, d121505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20452 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d120006 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120007 q = 1) (hb : d121506 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120007, d121506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120007, d121506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d120008 q = 1) (hb : d121507 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120008, d121507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d120008, d121507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d120009 q = 1) (hb : d121508 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120009, d121508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d120009, d121508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d120010 q = 1) (hb : d121509 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d120010, d121509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d120010, d121509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d120011 q = 1) (hb : d121510 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d120011, d121510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d120011, d121510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20454 (p : Pattern) (ha : d120017 p = 1) (hb : d121516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120012 q = 1) (hb : d121511 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d120012, d121511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120012, d121511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20453 q ha hb
  have h2 (q : Pattern) (ha : d120013 q = 1) (hb : d121512 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d120013, d121512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120013, d121512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120014 q = 1) (hb : d121513 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d120014, d121513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120014, d121513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120015 q = 1) (hb : d121514 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d120015, d121514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120015, d121514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120016 q = 1) (hb : d121515 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d120016, d121515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120016, d121515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120017 q = 1) (hb : d121516 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d120017, d121516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120017, d121516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20455 (p : Pattern) (ha : d120023 p = 1) (hb : d121522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d118942 q = 1) (hb : d121387 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d118942, d121387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20420 q ha hb
    | true =>
      simp only [d118942, d121387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20426 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d119171 q = 1) (hb : d121418 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d119171, d121418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119171, d121418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20433 q ha hb
  have h3 (q : Pattern) (ha : d119172 q = 1) (hb : d121419 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d119172, d121419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d119172, d121419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119429 q = 1) (hb : d121450 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d119429, d121450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119429, d121450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20440 q ha hb
  have h5 (q : Pattern) (ha : d119430 q = 1) (hb : d121451 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d119430, d121451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119430, d121451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119431 q = 1) (hb : d121452 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d119431, d121452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119431, d121452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d119728 q = 1) (hb : d121483 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d119728, d121483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119728, d121483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20447 q ha hb
  have h8 (q : Pattern) (ha : d119729 q = 1) (hb : d121484 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d119729, d121484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119729, d121484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d119730 q = 1) (hb : d121485 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d119730, d121485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d119730, d121485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119731 q = 1) (hb : d121486 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d119731, d121486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119731, d121486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120018 q = 1) (hb : d121517 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d120018, d121517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120018, d121517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20454 q ha hb
  have h12 (q : Pattern) (ha : d120019 q = 1) (hb : d121518 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d120019, d121518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120019, d121518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d120020 q = 1) (hb : d121519 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d120020, d121519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120020, d121519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d120021 q = 1) (hb : d121520 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d120021, d121520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d120021, d121520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d120022 q = 1) (hb : d121521 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d120022, d121521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120022, d121521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120023 q = 1) (hb : d121522 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d120023, d121522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d120023, d121522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro20456 (p : Pattern) (ha : d120029 p = 1) (hb : d121528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120024 q = 1) (hb : d121523 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d120024, d121523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20455 q ha hb
    | true =>
      simp only [d120024, d121523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120025 q = 1) (hb : d121524 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d120025, d121524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120025, d121524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120026 q = 1) (hb : d121525 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d120026, d121525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120026, d121525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120027 q = 1) (hb : d121526 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d120027, d121526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120027, d121526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120028 q = 1) (hb : d121527 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d120028, d121527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120028, d121527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120029 q = 1) (hb : d121528 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d120029, d121528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120029, d121528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20457 (p : Pattern) (ha : d120035 p = 1) (hb : d121534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120030 q = 1) (hb : d121529 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d120030, d121529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20456 q ha hb
    | true =>
      simp only [d120030, d121529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120031 q = 1) (hb : d121530 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d120031, d121530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120031, d121530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120032 q = 1) (hb : d121531 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d120032, d121531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120032, d121531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120033 q = 1) (hb : d121532 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d120033, d121532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120033, d121532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120034 q = 1) (hb : d121533 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d120034, d121533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120034, d121533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120035 q = 1) (hb : d121534 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d120035, d121534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120035, d121534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20458 (p : Pattern) (ha : d120041 p = 1) (hb : d121540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120036 q = 1) (hb : d121535 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d120036, d121535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20457 q ha hb
    | true =>
      simp only [d120036, d121535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120037 q = 1) (hb : d121536 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d120037, d121536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120037, d121536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120038 q = 1) (hb : d121537 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d120038, d121537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120038, d121537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120039 q = 1) (hb : d121538 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d120039, d121538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120039, d121538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120040 q = 1) (hb : d121539 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d120040, d121539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120040, d121539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120041 q = 1) (hb : d121540 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d120041, d121540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120041, d121540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20459 (p : Pattern) (ha : d120047 p = 1) (hb : d121546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120042 q = 1) (hb : d121541 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d120042, d121541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20458 q ha hb
    | true =>
      simp only [d120042, d121541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120043 q = 1) (hb : d121542 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d120043, d121542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120043, d121542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120044 q = 1) (hb : d121543 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d120044, d121543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120044, d121543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120045 q = 1) (hb : d121544 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d120045, d121544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120045, d121544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120046 q = 1) (hb : d121545 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d120046, d121545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120046, d121545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120047 q = 1) (hb : d121546 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d120047, d121546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120047, d121546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20460 (p : Pattern) (ha : d120053 p = 1) (hb : d121552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120048 q = 1) (hb : d121547 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d120048, d121547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20459 q ha hb
    | true =>
      simp only [d120048, d121547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120049 q = 1) (hb : d121548 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d120049, d121548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120049, d121548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120050 q = 1) (hb : d121549 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d120050, d121549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120050, d121549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120051 q = 1) (hb : d121550 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d120051, d121550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120051, d121550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120052 q = 1) (hb : d121551 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d120052, d121551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120052, d121551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120053 q = 1) (hb : d121552 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d120053, d121552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120053, d121552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20461 (p : Pattern) (ha : d120059 p = 1) (hb : d121558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120054 q = 1) (hb : d121553 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d120054, d121553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20460 q ha hb
    | true =>
      simp only [d120054, d121553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120055 q = 1) (hb : d121554 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d120055, d121554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120055, d121554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120056 q = 1) (hb : d121555 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d120056, d121555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120056, d121555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120057 q = 1) (hb : d121556 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d120057, d121556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120057, d121556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120058 q = 1) (hb : d121557 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d120058, d121557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120058, d121557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120059 q = 1) (hb : d121558 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d120059, d121558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120059, d121558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20462 (p : Pattern) (ha : d120065 p = 1) (hb : d121564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120060 q = 1) (hb : d121559 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d120060, d121559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20461 q ha hb
    | true =>
      simp only [d120060, d121559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d120061 q = 1) (hb : d121560 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d120061, d121560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120061, d121560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d120062 q = 1) (hb : d121561 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d120062, d121561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120062, d121561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d120063 q = 1) (hb : d121562 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d120063, d121562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120063, d121562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d120064 q = 1) (hb : d121563 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d120064, d121563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120064, d121563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d120065 q = 1) (hb : d121564 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d120065, d121564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120065, d121564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20463 (p : Pattern) (ha : d120136 p = 1) (hb : d121569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116848 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116854 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d116872 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120132 q = 1) (hb : d121565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d121565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120132, d121565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116772 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120133 q = 1) (hb : d121566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d121566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120133, d121566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120134 q = 1) (hb : d121567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d121567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120134, d121567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120135 q = 1) (hb : d121568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d121568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120135, d121568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120136 q = 1) (hb : d121569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120136, d121569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120136, d121569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20464 (p : Pattern) (ha : d120143 p = 1) (hb : d121574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116848 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116872 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120132 q = 1) (hb : d121565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d121565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120132, d121565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d116772 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d120133 q = 1) (hb : d121566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d121566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120133, d121566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120134 q = 1) (hb : d121567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d121567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120134, d121567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120135 q = 1) (hb : d121568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d121568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d121568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d116900 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d116904 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d116906 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120139 q = 1) (hb : d121570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d121570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120139, d121570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d116779 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120140 q = 1) (hb : d121571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d121571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120140, d121571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120141 q = 1) (hb : d121572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d121572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120141, d121572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120142 q = 1) (hb : d121573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d121573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120142, d121573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120143 q = 1) (hb : d121574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120143, d121574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120143, d121574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20465 (p : Pattern) (ha : d120334 p = 1) (hb : d121581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116906 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120139 q = 1) (hb : d121570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d121570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120139, d121570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116779 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120140 q = 1) (hb : d121571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d121571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120140, d121571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120141 q = 1) (hb : d121579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d121579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d121579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120142 q = 1) (hb : d121580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d121580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d121580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120334 q = 1) (hb : d121581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120334, d121581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120334, d121581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20466 (p : Pattern) (ha : d120378 p = 1) (hb : d121591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116945 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120374 q = 1) (hb : d121587 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120374, d121587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120374, d121587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120375 q = 1) (hb : d121588 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120375, d121588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120375, d121588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120376 q = 1) (hb : d121589 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120376, d121589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120376, d121589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120377 q = 1) (hb : d121590 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120377, d121590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120377, d121590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120378 q = 1) (hb : d121591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120378, d121591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120378, d121591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20467 (p : Pattern) (ha : d121355 p = 1) (hb : d121597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120144 q = 1) (hb : d121575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120144, d121575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20463 q ha hb
    | true =>
      simp only [d120144, d121575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20464 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120145 q = 1) (hb : d121576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120145, d121576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120145, d121576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121345 q = 1) (hb : d121577 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121345, d121577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121345, d121577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121346 q = 1) (hb : d121578 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121346, d121578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121346, d121578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120335 q = 1) (hb : d121582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120335, d121582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120335, d121582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20465 q ha hb
  have h8 (q : Pattern) (ha : d121347 q = 1) (hb : d121583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121347, d121583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121347, d121583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d121348 q = 1) (hb : d121584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121348, d121584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d121348, d121584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d121349 q = 1) (hb : d121585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121349, d121585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121349, d121585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121350 q = 1) (hb : d121586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121350, d121586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121350, d121586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120379 q = 1) (hb : d121592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120379, d121592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120379, d121592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20466 q ha hb
  have h13 (q : Pattern) (ha : d121351 q = 1) (hb : d121593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121351, d121593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121351, d121593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d121352 q = 1) (hb : d121594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121352, d121594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121352, d121594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d121353 q = 1) (hb : d121595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121353, d121595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d121353, d121595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d121354 q = 1) (hb : d121596 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121354, d121596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121354, d121596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121355 q = 1) (hb : d121597 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121355, d121597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d121355, d121597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro20468 (p : Pattern) (ha : d121361 p = 1) (hb : d121603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116827 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121356 q = 1) (hb : d121598 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121356, d121598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121356, d121598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20467 q ha hb
  have h3 (q : Pattern) (ha : d121357 q = 1) (hb : d121599 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121357, d121599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121357, d121599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121358 q = 1) (hb : d121600 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121358, d121600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121358, d121600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121359 q = 1) (hb : d121601 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121359, d121601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121359, d121601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121360 q = 1) (hb : d121602 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121360, d121602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121360, d121602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121361 q = 1) (hb : d121603 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121361, d121603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121361, d121603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20469 (p : Pattern) (ha : d120243 p = 1) (hb : d121608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117001 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117007 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d117025 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120239 q = 1) (hb : d121604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120239, d121604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120239, d121604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d117050 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120240 q = 1) (hb : d121605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120240, d121605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120240, d121605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120241 q = 1) (hb : d121606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120241, d121606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120241, d121606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120242 q = 1) (hb : d121607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120242, d121607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120242, d121607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120243 q = 1) (hb : d121608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120243, d121608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120243, d121608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20470 (p : Pattern) (ha : d120250 p = 1) (hb : d121613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d117001 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120172 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120239 q = 1) (hb : d121604 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120239, d121604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120239, d121604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d117050 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d120240 q = 1) (hb : d121605 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120240, d121605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120240, d121605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120241 q = 1) (hb : d121606 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120241, d121606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120241, d121606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120242 q = 1) (hb : d121607 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120242, d121607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120242, d121607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d117059 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d117063 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d117065 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120188 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120246 q = 1) (hb : d121609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120246, d121609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120246, d121609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117071 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120247 q = 1) (hb : d121610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120247, d121610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120247, d121610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120248 q = 1) (hb : d121611 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120248, d121611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120248, d121611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120249 q = 1) (hb : d121612 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120249, d121612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120249, d121612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120250 q = 1) (hb : d121613 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120250, d121613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120250, d121613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20471 (p : Pattern) (ha : d121364 p = 1) (hb : d121620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120188 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120246 q = 1) (hb : d121609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120246, d121609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120246, d121609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d117071 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120247 q = 1) (hb : d121610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120247, d121610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120247, d121610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120248 q = 1) (hb : d121618 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120248, d121618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120248, d121618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120249 q = 1) (hb : d121619 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120249, d121619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120249, d121619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121364 q = 1) (hb : d121620 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121364, d121620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121364, d121620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20472 (p : Pattern) (ha : d121374 p = 1) (hb : d121630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120221 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121370 q = 1) (hb : d121626 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121370, d121626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121370, d121626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d117134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121371 q = 1) (hb : d121627 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121371, d121627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121371, d121627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121372 q = 1) (hb : d121628 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121372, d121628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121372, d121628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121373 q = 1) (hb : d121629 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121373, d121629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121373, d121629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121374 q = 1) (hb : d121630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121374, d121630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121374, d121630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20473 (p : Pattern) (ha : d121380 p = 1) (hb : d121636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116995 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120251 q = 1) (hb : d121614 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120251, d121614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20469 q ha hb
    | true =>
      simp only [d120251, d121614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20470 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117078 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120252 q = 1) (hb : d121615 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120252, d121615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120252, d121615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121362 q = 1) (hb : d121616 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121362, d121616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121362, d121616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121363 q = 1) (hb : d121617 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121363, d121617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121363, d121617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121365 q = 1) (hb : d121621 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121365, d121621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121365, d121621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20471 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d117087 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d121366 q = 1) (hb : d121622 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121366, d121622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121366, d121622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d121367 q = 1) (hb : d121623 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121367, d121623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121367, d121623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121368 q = 1) (hb : d121624 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121368, d121624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d121368, d121624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d121369 q = 1) (hb : d121625 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121369, d121625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121369, d121625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d121375 q = 1) (hb : d121631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121375, d121631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121375, d121631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20472 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117145 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d121376 q = 1) (hb : d121632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121376, d121632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121376, d121632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d121377 q = 1) (hb : d121633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121377, d121633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121377, d121633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121378 q = 1) (hb : d121634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121378, d121634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d121378, d121634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d121379 q = 1) (hb : d121635 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121379, d121635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d121379, d121635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d121380 q = 1) (hb : d121636 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121380, d121636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121380, d121636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20474 (p : Pattern) (ha : d121386 p = 1) (hb : d121642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121381 q = 1) (hb : d121637 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121381, d121637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121381, d121637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20473 q ha hb
  have h2 (q : Pattern) (ha : d121382 q = 1) (hb : d121638 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121382, d121638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121382, d121638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d121383 q = 1) (hb : d121639 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121383, d121639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121383, d121639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121384 q = 1) (hb : d121640 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121384, d121640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121384, d121640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121385 q = 1) (hb : d121641 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121385, d121641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121385, d121641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121386 q = 1) (hb : d121642 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121386, d121642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121386, d121642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20475 (p : Pattern) (ha : d120422 p = 1) (hb : d121648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117218 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d117244 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120417 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120418 q = 1) (hb : d121644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120418, d121644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120418, d121644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d117282 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120419 q = 1) (hb : d121645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120419, d121645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120419, d121645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120420 q = 1) (hb : d121646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120420, d121646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120420, d121646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120421 q = 1) (hb : d121647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120421, d121647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120421, d121647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120422 q = 1) (hb : d121648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120422, d121648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120422, d121648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20476 (p : Pattern) (ha : d120432 p = 1) (hb : d121653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d117209 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120417 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120418 q = 1) (hb : d121644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120418, d121644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120418, d121644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d117282 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d120419 q = 1) (hb : d121645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120419, d121645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120419, d121645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120420 q = 1) (hb : d121646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120420, d121646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120420, d121646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120421 q = 1) (hb : d121647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120421, d121647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120421, d121647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d117292 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d117297 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d117299 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120427 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120428 q = 1) (hb : d121649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120428, d121649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120428, d121649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117306 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120429 q = 1) (hb : d121650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120429, d121650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120429, d121650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120430 q = 1) (hb : d121651 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120430, d121651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120430, d121651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120431 q = 1) (hb : d121652 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120431, d121652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120431, d121652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120432 q = 1) (hb : d121653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120432, d121653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120432, d121653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20477 (p : Pattern) (ha : d121390 p = 1) (hb : d121660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117299 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120428 q = 1) (hb : d121649 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120428, d121649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120428, d121649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d117306 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120429 q = 1) (hb : d121650 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120429, d121650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120429, d121650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120430 q = 1) (hb : d121658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120430, d121658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120430, d121658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120431 q = 1) (hb : d121659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120431, d121659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120431, d121659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121390 q = 1) (hb : d121660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121390, d121660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121390, d121660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20478 (p : Pattern) (ha : d121405 p = 1) (hb : d121670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d121400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121401 q = 1) (hb : d121666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121401, d121666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121401, d121666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d117422 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121402 q = 1) (hb : d121667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121402, d121667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121402, d121667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121403 q = 1) (hb : d121668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121403, d121668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121403, d121668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121404 q = 1) (hb : d121669 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121404, d121669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121404, d121669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121405 q = 1) (hb : d121670 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121405, d121670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121405, d121670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20479 (p : Pattern) (ha : d121411 p = 1) (hb : d121676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d117201 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120433 q = 1) (hb : d121654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120433, d121654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20475 q ha hb
    | true =>
      simp only [d120433, d121654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20476 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120434 q = 1) (hb : d121655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120434, d121655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120434, d121655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121388 q = 1) (hb : d121656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121388, d121656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121388, d121656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121389 q = 1) (hb : d121657 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121389, d121657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121389, d121657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121391 q = 1) (hb : d121661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121391, d121661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121391, d121661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20477 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d117333 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d121392 q = 1) (hb : d121662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121392, d121662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121392, d121662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d121393 q = 1) (hb : d121663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121393, d121663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121393, d121663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121394 q = 1) (hb : d121664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121394, d121664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d121394, d121664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d121395 q = 1) (hb : d121665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121395, d121665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121395, d121665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d121406 q = 1) (hb : d121671 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121406, d121671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121406, d121671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20478 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117438 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d121407 q = 1) (hb : d121672 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121407, d121672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121407, d121672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d121408 q = 1) (hb : d121673 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121408, d121673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121408, d121673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121409 q = 1) (hb : d121674 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121409, d121674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d121409, d121674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d121410 q = 1) (hb : d121675 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121410, d121675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d121410, d121675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d121411 q = 1) (hb : d121676 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121411, d121676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121411, d121676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20480 (p : Pattern) (ha : d121417 p = 1) (hb : d121682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121412 q = 1) (hb : d121677 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121412, d121677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121412, d121677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20479 q ha hb
  have h2 (q : Pattern) (ha : d121413 q = 1) (hb : d121678 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121413, d121678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121413, d121678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d121414 q = 1) (hb : d121679 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121414, d121679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121414, d121679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121415 q = 1) (hb : d121680 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121415, d121680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121415, d121680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121416 q = 1) (hb : d121681 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121416, d121681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121416, d121681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121417 q = 1) (hb : d121682 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121417, d121682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121417, d121682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20481 (p : Pattern) (ha : d120647 p = 1) (hb : d121689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117517 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117526 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d117552 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120642 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120643 q = 1) (hb : d121685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120643, d121685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120643, d121685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d117599 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120644 q = 1) (hb : d121686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120644, d121686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120644, d121686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120645 q = 1) (hb : d121687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120645, d121687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120645, d121687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120646 q = 1) (hb : d121688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120646, d121688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120646, d121688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120647 q = 1) (hb : d121689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120647, d121689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120647, d121689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20482 (p : Pattern) (ha : d120657 p = 1) (hb : d121694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d117517 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117526 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120642 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120643 q = 1) (hb : d121685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120643, d121685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120643, d121685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d117599 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d120644 q = 1) (hb : d121686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120644, d121686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120644, d121686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120645 q = 1) (hb : d121687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120645, d121687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120645, d121687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120646 q = 1) (hb : d121688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120646, d121688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120646, d121688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d117609 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d117614 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d117616 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120652 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120653 q = 1) (hb : d121690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120653, d121690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120653, d121690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117623 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120654 q = 1) (hb : d121691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120654, d121691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120654, d121691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120655 q = 1) (hb : d121692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120655, d121692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120655, d121692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120656 q = 1) (hb : d121693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120656, d121693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120656, d121693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120657 q = 1) (hb : d121694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120657, d121694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120657, d121694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20483 (p : Pattern) (ha : d121422 p = 1) (hb : d121701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117616 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120653 q = 1) (hb : d121690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120653, d121690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120653, d121690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d117623 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120654 q = 1) (hb : d121691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120654, d121691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120654, d121691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120655 q = 1) (hb : d121699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120655, d121699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120655, d121699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120656 q = 1) (hb : d121700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120656, d121700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120656, d121700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121422 q = 1) (hb : d121701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121422, d121701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121422, d121701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20484 (p : Pattern) (ha : d121437 p = 1) (hb : d121711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d121432 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121433 q = 1) (hb : d121707 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121433, d121707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121433, d121707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d117762 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121434 q = 1) (hb : d121708 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121434, d121708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121434, d121708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121435 q = 1) (hb : d121709 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121435, d121709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121435, d121709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121436 q = 1) (hb : d121710 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121436, d121710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121436, d121710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121437 q = 1) (hb : d121711 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121437, d121711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121437, d121711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20485 (p : Pattern) (ha : d121443 p = 1) (hb : d121717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d117509 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120658 q = 1) (hb : d121695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120658, d121695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20481 q ha hb
    | true =>
      simp only [d120658, d121695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20482 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117641 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120659 q = 1) (hb : d121696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120659, d121696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120659, d121696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121420 q = 1) (hb : d121697 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121420, d121697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121420, d121697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121421 q = 1) (hb : d121698 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121421, d121698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121421, d121698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121423 q = 1) (hb : d121702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121423, d121702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121423, d121702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20483 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d117650 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d121424 q = 1) (hb : d121703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121424, d121703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121424, d121703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d121425 q = 1) (hb : d121704 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121425, d121704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121425, d121704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121426 q = 1) (hb : d121705 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121426, d121705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d121426, d121705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d121427 q = 1) (hb : d121706 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121427, d121706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121427, d121706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d121438 q = 1) (hb : d121712 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121438, d121712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121438, d121712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20484 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117778 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d121439 q = 1) (hb : d121713 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121439, d121713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121439, d121713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d121440 q = 1) (hb : d121714 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121440, d121714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121440, d121714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121441 q = 1) (hb : d121715 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121441, d121715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d121441, d121715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d121442 q = 1) (hb : d121716 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121442, d121716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d121442, d121716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d121443 q = 1) (hb : d121717 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121443, d121717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121443, d121717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20486 (p : Pattern) (ha : d121449 p = 1) (hb : d121723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121444 q = 1) (hb : d121718 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121444, d121718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121444, d121718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20485 q ha hb
  have h2 (q : Pattern) (ha : d121445 q = 1) (hb : d121719 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121445, d121719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121445, d121719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d121446 q = 1) (hb : d121720 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121446, d121720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121446, d121720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121447 q = 1) (hb : d121721 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121447, d121721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121447, d121721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121448 q = 1) (hb : d121722 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121448, d121722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121448, d121722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121449 q = 1) (hb : d121723 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121449, d121723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121449, d121723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20487 (p : Pattern) (ha : d120875 p = 1) (hb : d121731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117875 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d117910 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120870 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120871 q = 1) (hb : d121727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120871, d121727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120871, d121727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d117965 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120872 q = 1) (hb : d121728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120872, d121728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120872, d121728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120873 q = 1) (hb : d121729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120873, d121729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120873, d121729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120874 q = 1) (hb : d121730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120874, d121730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120874, d121730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120875 q = 1) (hb : d121731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120875, d121731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120875, d121731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20488 (p : Pattern) (ha : d120885 p = 1) (hb : d121736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d117866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117875 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117910 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120871 q = 1) (hb : d121727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120871, d121727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120871, d121727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d117965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d120872 q = 1) (hb : d121728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120872, d121728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120872, d121728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120873 q = 1) (hb : d121729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120873, d121729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120873, d121729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120874 q = 1) (hb : d121730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120874, d121730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120874, d121730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d117975 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d117980 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d117983 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120880 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120881 q = 1) (hb : d121732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120881, d121732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120881, d121732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117990 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120882 q = 1) (hb : d121733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120882, d121733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120882, d121733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120883 q = 1) (hb : d121734 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120883, d121734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120883, d121734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120884 q = 1) (hb : d121735 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120884, d121735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120884, d121735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120885 q = 1) (hb : d121736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120885, d121736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120885, d121736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20489 (p : Pattern) (ha : d121455 p = 1) (hb : d121743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d117983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120881 q = 1) (hb : d121732 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120881, d121732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120881, d121732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d117990 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120882 q = 1) (hb : d121733 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120882, d121733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120882, d121733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120883 q = 1) (hb : d121741 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120883, d121741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120883, d121741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120884 q = 1) (hb : d121742 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120884, d121742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120884, d121742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121455 q = 1) (hb : d121743 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121455, d121743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121455, d121743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20490 (p : Pattern) (ha : d121470 p = 1) (hb : d121753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118096 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d121465 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121466 q = 1) (hb : d121749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121466, d121749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121466, d121749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118155 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121467 q = 1) (hb : d121750 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121467, d121750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121467, d121750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121468 q = 1) (hb : d121751 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121468, d121751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121468, d121751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121469 q = 1) (hb : d121752 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121469, d121752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121469, d121752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121470 q = 1) (hb : d121753 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121470, d121753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121470, d121753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20491 (p : Pattern) (ha : d121476 p = 1) (hb : d121759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d117858 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120886 q = 1) (hb : d121737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120886, d121737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20487 q ha hb
    | true =>
      simp only [d120886, d121737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20488 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118013 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120887 q = 1) (hb : d121738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120887, d121738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120887, d121738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121453 q = 1) (hb : d121739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121453, d121739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121453, d121739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121454 q = 1) (hb : d121740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121454, d121740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121454, d121740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121456 q = 1) (hb : d121744 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121456, d121744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121456, d121744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20489 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d118022 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d121457 q = 1) (hb : d121745 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121457, d121745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121457, d121745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d121458 q = 1) (hb : d121746 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121458, d121746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121458, d121746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121459 q = 1) (hb : d121747 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121459, d121747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d121459, d121747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d121460 q = 1) (hb : d121748 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121460, d121748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121460, d121748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d121471 q = 1) (hb : d121754 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121471, d121754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121471, d121754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20490 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d118171 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d121472 q = 1) (hb : d121755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121472, d121755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121472, d121755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d121473 q = 1) (hb : d121756 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121473, d121756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121473, d121756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121474 q = 1) (hb : d121757 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121474, d121757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d121474, d121757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d121475 q = 1) (hb : d121758 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121475, d121758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d121475, d121758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d121476 q = 1) (hb : d121759 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121476, d121759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121476, d121759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20492 (p : Pattern) (ha : d121482 p = 1) (hb : d121765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121477 q = 1) (hb : d121760 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121477, d121760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121477, d121760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20491 q ha hb
  have h2 (q : Pattern) (ha : d121478 q = 1) (hb : d121761 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121478, d121761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121478, d121761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d121479 q = 1) (hb : d121762 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121479, d121762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121479, d121762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121480 q = 1) (hb : d121763 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121480, d121763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121480, d121763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121481 q = 1) (hb : d121764 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121481, d121764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121481, d121764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121482 q = 1) (hb : d121765 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121482, d121765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121482, d121765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20493 (p : Pattern) (ha : d121104 p = 1) (hb : d121774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118260 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118269 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d118299 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d121099 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121100 q = 1) (hb : d121770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121100, d121770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121100, d121770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118354 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d121101 q = 1) (hb : d121771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121101, d121771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d121101, d121771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121102 q = 1) (hb : d121772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121102, d121772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121102, d121772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d121103 q = 1) (hb : d121773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121103, d121773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121103, d121773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d121104 q = 1) (hb : d121774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121104, d121774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121104, d121774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20494 (p : Pattern) (ha : d121114 p = 1) (hb : d121779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118260 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118299 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d121099 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d121100 q = 1) (hb : d121770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121100, d121770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d121100, d121770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d118354 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d121101 q = 1) (hb : d121771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121101, d121771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121101, d121771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121102 q = 1) (hb : d121772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121102, d121772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121102, d121772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121103 q = 1) (hb : d121773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121103, d121773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121103, d121773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d118364 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d118369 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d118372 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d121109 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d121110 q = 1) (hb : d121775 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121110, d121775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d121110, d121775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d118379 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d121111 q = 1) (hb : d121776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121111, d121776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121111, d121776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d121112 q = 1) (hb : d121777 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121112, d121777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d121112, d121777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d121113 q = 1) (hb : d121778 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121113, d121778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121113, d121778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d121114 q = 1) (hb : d121779 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121114, d121779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d121114, d121779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20495 (p : Pattern) (ha : d121489 p = 1) (hb : d121786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d121109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121110 q = 1) (hb : d121775 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121110, d121775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121110, d121775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121111 q = 1) (hb : d121776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121111, d121776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121111, d121776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121112 q = 1) (hb : d121784 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121112, d121784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121112, d121784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121113 q = 1) (hb : d121785 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121113, d121785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121113, d121785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121489 q = 1) (hb : d121786 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121489, d121786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121489, d121786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20496 (p : Pattern) (ha : d121504 p = 1) (hb : d121796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d121499 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121500 q = 1) (hb : d121792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d121500, d121792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121500, d121792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118539 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121501 q = 1) (hb : d121793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d121501, d121793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121501, d121793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121502 q = 1) (hb : d121794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d121502, d121794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121502, d121794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121503 q = 1) (hb : d121795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d121503, d121795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121503, d121795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d121504 q = 1) (hb : d121796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d121504, d121796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121504, d121796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20497 (p : Pattern) (ha : d121510 p = 1) (hb : d121802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121115 q = 1) (hb : d121780 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121115, d121780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20493 q ha hb
    | true =>
      simp only [d121115, d121780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20494 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118402 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121116 q = 1) (hb : d121781 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121116, d121781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121116, d121781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121487 q = 1) (hb : d121782 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121487, d121782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121487, d121782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121488 q = 1) (hb : d121783 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121488, d121783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121488, d121783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121490 q = 1) (hb : d121787 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121490, d121787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121490, d121787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20495 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d118411 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d121491 q = 1) (hb : d121788 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121491, d121788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121491, d121788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d121492 q = 1) (hb : d121789 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121492, d121789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121492, d121789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121493 q = 1) (hb : d121790 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121493, d121790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d121493, d121790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d121494 q = 1) (hb : d121791 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121494, d121791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121494, d121791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d121505 q = 1) (hb : d121797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d121505, d121797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d121505, d121797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20496 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d118555 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d121506 q = 1) (hb : d121798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121506, d121798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121506, d121798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d121507 q = 1) (hb : d121799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121507, d121799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121507, d121799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121508 q = 1) (hb : d121800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121508, d121800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d121508, d121800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d121509 q = 1) (hb : d121801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121509, d121801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d121509, d121801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d121510 q = 1) (hb : d121802 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121510, d121802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121510, d121802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20498 (p : Pattern) (ha : d121516 p = 1) (hb : d121808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d121511 q = 1) (hb : d121803 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121511, d121803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121511, d121803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20497 q ha hb
  have h2 (q : Pattern) (ha : d121512 q = 1) (hb : d121804 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121512, d121804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121512, d121804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d121513 q = 1) (hb : d121805 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121513, d121805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121513, d121805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121514 q = 1) (hb : d121806 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121514, d121806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121514, d121806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121515 q = 1) (hb : d121807 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121515, d121807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121515, d121807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121516 q = 1) (hb : d121808 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121516, d121808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121516, d121808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20499 (p : Pattern) (ha : d121522 p = 1) (hb : d121814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d121387 q = 1) (hb : d121643 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d121387, d121643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20468 q ha hb
    | true =>
      simp only [d121387, d121643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20474 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121418 q = 1) (hb : d121683 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d121418, d121683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121418, d121683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20480 q ha hb
  have h3 (q : Pattern) (ha : d121419 q = 1) (hb : d121684 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d121419, d121684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121419, d121684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121450 q = 1) (hb : d121724 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d121450, d121724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121450, d121724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20486 q ha hb
  have h5 (q : Pattern) (ha : d121451 q = 1) (hb : d121725 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d121451, d121725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121451, d121725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121452 q = 1) (hb : d121726 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d121452, d121726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121452, d121726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121483 q = 1) (hb : d121766 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d121483, d121766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121483, d121766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20492 q ha hb
  have h8 (q : Pattern) (ha : d121484 q = 1) (hb : d121767 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d121484, d121767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121484, d121767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d121485 q = 1) (hb : d121768 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d121485, d121768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121485, d121768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d121486 q = 1) (hb : d121769 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d121486, d121769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121486, d121769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d121517 q = 1) (hb : d121809 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d121517, d121809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121517, d121809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20498 q ha hb
  have h12 (q : Pattern) (ha : d121518 q = 1) (hb : d121810 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d121518, d121810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121518, d121810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d121519 q = 1) (hb : d121811 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d121519, d121811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121519, d121811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d121520 q = 1) (hb : d121812 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d121520, d121812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121520, d121812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d121521 q = 1) (hb : d121813 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d121521, d121813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d121521, d121813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d121522 q = 1) (hb : d121814 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d121522, d121814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121522, d121814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
end NetHack.Soko22Hazard87
