import NetHack.Soko22Hazard87.AndIntroBlocks0424
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro106250 (p : Pattern) (ha : d373313 p = 1) (hb : d374771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373122 q = 1) (hb : d374550 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373122, d374550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106205 q ha hb
    | true =>
      simp only [d373122, d374550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106177 q ha hb
  have h2 (q : Pattern) (ha : d373123 q = 1) (hb : d374551 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373123, d374551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373123, d374551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373124 q = 1) (hb : d374552 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373124, d374552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373124, d374552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341271 q = 1) (hb : d374404 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d341271, d374404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106177 q ha hb
    | true =>
      simp only [d341271, d374404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106156 q ha hb
  have h5 (q : Pattern) (ha : d341272 q = 1) (hb : d374405 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d341272, d374405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341272, d374405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341273 q = 1) (hb : d374406 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d341273, d374406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341273, d374406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373125 q = 1) (hb : d374553 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373125, d374553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373125, d374553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341664 q = 1) (hb : d374769 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d341664, d374769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341664, d374769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373312 q = 1) (hb : d374770 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d373312, d374770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373312, d374770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373313 q = 1) (hb : d374771 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d373313, d374771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373313, d374771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro106251 (p : Pattern) (ha : d373319 p = 1) (hb : d374777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373310 q = 1) (hb : d374767 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373310, d374767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106249 q ha hb
    | true =>
      simp only [d373310, d374767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373311 q = 1) (hb : d374768 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373311, d374768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373311, d374768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373314 q = 1) (hb : d374772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373314, d374772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106250 q ha hb
    | true =>
      simp only [d373314, d374772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373315 q = 1) (hb : d374773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373315, d374773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373315, d374773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373316 q = 1) (hb : d374774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373316, d374774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373316, d374774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373317 q = 1) (hb : d374775 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373317, d374775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373317, d374775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373318 q = 1) (hb : d374776 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373318, d374776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373318, d374776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373319 q = 1) (hb : d374777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373319, d374777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373319, d374777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106252 (p : Pattern) (ha : d373323 p = 1) (hb : d374785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373314 q = 1) (hb : d374772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373314, d374772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106250 q ha hb
    | true =>
      simp only [d373314, d374772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373315 q = 1) (hb : d374773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373315, d374773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373315, d374773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d341675 q = 1) (hb : d374780 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d341675, d374780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106216 q ha hb
    | true =>
      simp only [d341675, d374780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d341676 q = 1) (hb : d374781 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d341676, d374781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341676, d374781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373320 q = 1) (hb : d374782 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373320, d374782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373320, d374782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373321 q = 1) (hb : d374783 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373321, d374783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373321, d374783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373322 q = 1) (hb : d374784 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373322, d374784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373322, d374784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373323 q = 1) (hb : d374785 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373323, d374785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373323, d374785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106253 (p : Pattern) (ha : d373330 p = 1) (hb : d374791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373314 q = 1) (hb : d374772 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373314, d374772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106250 q ha hb
    | true =>
      simp only [d373314, d374772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373315 q = 1) (hb : d374773 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373315, d374773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373315, d374773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373327 q = 1) (hb : d374788 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373327, d374788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373327, d374788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373328 q = 1) (hb : d374789 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373328, d374789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373328, d374789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373329 q = 1) (hb : d374790 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373329, d374790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373329, d374790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373330 q = 1) (hb : d374791 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373330, d374791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373330, d374791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106254 (p : Pattern) (ha : d373336 p = 1) (hb : d374797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373324 q = 1) (hb : d374786 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373324, d374786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106251 q ha hb
    | true =>
      simp only [d373324, d374786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106252 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373326 q = 1) (hb : d374787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373326, d374787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373326, d374787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d373331 q = 1) (hb : d374792 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373331, d374792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106253 q ha hb
    | true =>
      simp only [d373331, d374792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373332 q = 1) (hb : d374793 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373332, d374793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373332, d374793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373333 q = 1) (hb : d374794 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373333, d374794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373333, d374794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373334 q = 1) (hb : d374795 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373334, d374795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373334, d374795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373335 q = 1) (hb : d374796 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373335, d374796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373335, d374796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373336 q = 1) (hb : d374797 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373336, d374797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373336, d374797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro106255 (p : Pattern) (ha : d373342 p = 1) (hb : d374814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373167 q = 1) (hb : d374610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373167, d374610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373167, d374610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106221 q ha hb
  have h2 (q : Pattern) (ha : d373168 q = 1) (hb : d374611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373168, d374611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373168, d374611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373176 q = 1) (hb : d374620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373176, d374620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106221 q ha hb
    | true =>
      simp only [d373176, d374620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106223 q ha hb
  have h4 (q : Pattern) (ha : d373177 q = 1) (hb : d374621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373177, d374621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373177, d374621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373178 q = 1) (hb : d374622 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373178, d374622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373178, d374622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373272 q = 1) (hb : d374715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373272, d374715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106237 q ha hb
    | true =>
      simp only [d373272, d374715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106244 q ha hb
  have h7 (q : Pattern) (ha : d373274 q = 1) (hb : d374728 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373274, d374728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106245 q ha hb
    | true =>
      simp only [d373274, d374728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106214 q ha hb
  have h8 (q : Pattern) (ha : d373275 q = 1) (hb : d374729 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373275, d374729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373275, d374729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373276 q = 1) (hb : d374730 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373276, d374730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373276, d374730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d373277 q = 1) (hb : d374731 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373277, d374731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373277, d374731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373281 q = 1) (hb : d374735 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373281, d374735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373281, d374735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106246 q ha hb
  have h12 (q : Pattern) (ha : d341632 q = 1) (hb : d374737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341632, d374737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341632, d374737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106215 q ha hb
  have h13 (q : Pattern) (ha : d373282 q = 1) (hb : d374738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373282, d374738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373282, d374738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373283 q = 1) (hb : d374739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373283, d374739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373283, d374739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373284 q = 1) (hb : d374740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373284, d374740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d373284, d374740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d373285 q = 1) (hb : d374741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373285, d374741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373285, d374741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d373337 q = 1) (hb : d374798 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373337, d374798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373337, d374798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106254 q ha hb
  have h18 (q : Pattern) (ha : d341705 q = 1) (hb : d374809 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341705, d374809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341705, d374809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106218 q ha hb
  have h19 (q : Pattern) (ha : d373338 q = 1) (hb : d374810 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373338, d374810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373338, d374810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d373339 q = 1) (hb : d374811 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373339, d374811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d373339, d374811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d373340 q = 1) (hb : d374812 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373340, d374812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d373340, d374812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d373341 q = 1) (hb : d374813 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373341, d374813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d373341, d374813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d373342 q = 1) (hb : d374814 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d373342, d374814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373342, d374814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro106256 (p : Pattern) (ha : d373348 p = 1) (hb : d374820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373343 q = 1) (hb : d374815 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d373343, d374815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373343, d374815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106255 q ha hb
  have h2 (q : Pattern) (ha : d373344 q = 1) (hb : d374816 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d373344, d374816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373344, d374816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373345 q = 1) (hb : d374817 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d373345, d374817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373345, d374817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373346 q = 1) (hb : d374818 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d373346, d374818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373346, d374818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373347 q = 1) (hb : d374819 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d373347, d374819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373347, d374819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373348 q = 1) (hb : d374820 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d373348, d374820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373348, d374820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106257 (p : Pattern) (ha : d373362 p = 1) (hb : d374643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373352 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d373353 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373354 q = 1) (hb : d374640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373354, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373354, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373067 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373067, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373067, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373068 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373068, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373068, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373193 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373193, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106229 q hb ha
    | true =>
      simp only [d373193, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373194 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373194, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373194, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373195 q = 1) (hb : d374464 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373195, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373195, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373355 q = 1) (hb : d374641 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373355, d374641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373355, d374641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373356 q = 1) (hb : d374642 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373356, d374642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373356, d374642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d341092 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d373357 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106165 q hb ha
    | true =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d373358 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373359 q = 1) (hb : d374464 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373359, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373359, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46871 q = 1) (hb : d341093 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106147 q ha hb
    | true =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d341094 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d373198 q = 1) (hb : d374351 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373198, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373198, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d373360 q = 1) (hb : d374465 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373360, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373360, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d373361 q = 1) (hb : d374466 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373361, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d373361, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d373362 q = 1) (hb : d374643 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373362, d374643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373362, d374643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro106258 (p : Pattern) (ha : d373374 p = 1) (hb : d374650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373352 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373353 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373357 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106165 q hb ha
    | true =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373358 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d373359 q = 1) (hb : d374464 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373359, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373359, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341205 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341205, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106165 q hb ha
    | true =>
      simp only [d341205, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d341206 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341206, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341206, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d46871 q = 1) (hb : d341093 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106147 q ha hb
    | true =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d341094 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d341207 q = 1) (hb : d374351 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341207, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341207, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373367 q = 1) (hb : d374465 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373367, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373367, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373368 q = 1) (hb : d374466 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373368, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373368, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d373370 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d356207 q = 1) (hb : d373371 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d356207, d373371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d356207, d373371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h17 (q : Pattern) (ha : d373372 q = 1) (hb : d374648 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373372, d374648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d373372, d374648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h18 (q : Pattern) (ha : d373373 q = 1) (hb : d374649 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373373, d374649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373373, d374649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h19 (q : Pattern) (ha : d373374 q = 1) (hb : d374650 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373374, d374650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d373374, d374650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106259 (p : Pattern) (ha : d373383 p = 1) (hb : d374659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373352 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373353 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d373206 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373380 q = 1) (hb : d374656 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373380, d374656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373380, d374656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373381 q = 1) (hb : d374657 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373381, d374657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373381, d374657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d373382 q = 1) (hb : d374658 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373382, d374658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373382, d374658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d373370 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d46871 q = 1) (hb : d341093 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106147 q ha hb
    | true =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d341094 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h11 (q : Pattern) (ha : d356207 q = 1) (hb : d373371 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d356207, d373371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d356207, d373371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d373372 q = 1) (hb : d374648 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373372, d374648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d373372, d374648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d373373 q = 1) (hb : d374649 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373373, d374649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d373373, d374649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h14 (q : Pattern) (ha : d373383 q = 1) (hb : d374659 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373383, d374659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373383, d374659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro106260 (p : Pattern) (ha : d373391 p = 1) (hb : d374823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373357 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106165 q hb ha
    | true =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373358 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d46871 q = 1) (hb : d341093 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106147 q ha hb
    | true =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d341094 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d373388 q = 1) (hb : d374351 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373388, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373388, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341095 q = 1) (hb : d355777 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341095, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341095, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d373389 q = 1) (hb : d374352 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373389, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373389, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373390 q = 1) (hb : d374353 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373390, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373390, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d373391 q = 1) (hb : d374823 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373391, d374823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373391, d374823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h10 p ha hb
theorem andIntro106261 (p : Pattern) (ha : d373397 p = 1) (hb : d374829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373363 q = 1) (hb : d374644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373363, d374644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106257 q ha hb
    | true =>
      simp only [d373363, d374644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373364 q = 1) (hb : d374645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373364, d374645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373364, d374645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373365 q = 1) (hb : d374646 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373365, d374646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373365, d374646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373366 q = 1) (hb : d374647 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373366, d374647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373366, d374647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373375 q = 1) (hb : d374651 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373375, d374651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106258 q ha hb
    | true =>
      simp only [d373375, d374651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373376 q = 1) (hb : d374652 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373376, d374652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373376, d374652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373377 q = 1) (hb : d374653 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373377, d374653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373377, d374653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373378 q = 1) (hb : d374654 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373378, d374654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373378, d374654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373379 q = 1) (hb : d374655 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373379, d374655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373379, d374655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373384 q = 1) (hb : d374660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106259 q ha hb
    | true =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373385 q = 1) (hb : d374661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d373386 q = 1) (hb : d374662 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373386, d374662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373386, d374662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373387 q = 1) (hb : d374663 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373387, d374663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d373387, d374663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d373394 q = 1) (hb : d374826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d373395 q = 1) (hb : d374827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d373396 q = 1) (hb : d374828 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373396, d374828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373396, d374828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d373397 q = 1) (hb : d374829 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373397, d374829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373397, d374829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106262 (p : Pattern) (ha : d373398 p = 1) (hb : d374467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373352 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373353 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341092 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373357 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106165 q hb ha
    | true =>
      simp only [d373357, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373358 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373358, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d373359 q = 1) (hb : d374464 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373359, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373359, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341205 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d341205, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106165 q hb ha
    | true =>
      simp only [d341205, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d341206 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341206, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341206, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d46871 q = 1) (hb : d341093 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106147 q ha hb
    | true =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d341094 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d341207 q = 1) (hb : d374351 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341207, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341207, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373367 q = 1) (hb : d374465 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373367, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373367, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373368 q = 1) (hb : d374466 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373368, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373368, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h15 (q : Pattern) (ha : d373388 q = 1) (hb : d374351 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373388, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373388, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h16 (q : Pattern) (ha : d341095 q = 1) (hb : d355777 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d341095, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341095, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h17 (q : Pattern) (ha : d373389 q = 1) (hb : d374352 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373389, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373389, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d373390 q = 1) (hb : d374353 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373390, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373390, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h19 (q : Pattern) (ha : d373398 q = 1) (hb : d374467 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373398, d374467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d373398, d374467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106263 (p : Pattern) (ha : d373405 p = 1) (hb : d374832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373399 q = 1) (hb : d374468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373399, d374468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106262 q ha hb
    | true =>
      simp only [d373399, d374468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373400 q = 1) (hb : d374469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373400, d374469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373400, d374469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373401 q = 1) (hb : d374470 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373401, d374470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373401, d374470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373402 q = 1) (hb : d374471 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373402, d374471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373402, d374471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373394 q = 1) (hb : d374826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373395 q = 1) (hb : d374827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373403 q = 1) (hb : d374830 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373403, d374830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373403, d374830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373404 q = 1) (hb : d374831 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373404, d374831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373404, d374831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373405 q = 1) (hb : d374832 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373405, d374832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373405, d374832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106264 (p : Pattern) (ha : d373409 p = 1) (hb : d374836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373394 q = 1) (hb : d374826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373395 q = 1) (hb : d374827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373404 q = 1) (hb : d374831 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373404, d374831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373404, d374831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373409 q = 1) (hb : d374836 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373409, d374836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373409, d374836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106265 (p : Pattern) (ha : d373416 p = 1) (hb : d374843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373406 q = 1) (hb : d374833 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373406, d374833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106261 q ha hb
    | true =>
      simp only [d373406, d374833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106263 q ha hb
  have h2 (q : Pattern) (ha : d373407 q = 1) (hb : d374834 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373407, d374834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373407, d374834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373408 q = 1) (hb : d374835 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373408, d374835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373408, d374835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373410 q = 1) (hb : d374837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373410, d374837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106263 q ha hb
    | true =>
      simp only [d373410, d374837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106264 q ha hb
  have h5 (q : Pattern) (ha : d373411 q = 1) (hb : d374838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373411, d374838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373411, d374838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373412 q = 1) (hb : d374839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373412, d374839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373412, d374839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373413 q = 1) (hb : d374840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373413, d374840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373413, d374840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373414 q = 1) (hb : d374841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373414, d374841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373414, d374841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373415 q = 1) (hb : d374842 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d373415, d374842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373415, d374842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373416 q = 1) (hb : d374843 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d373416, d374843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373416, d374843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro106266 (p : Pattern) (ha : d373420 p = 1) (hb : d374847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373410 q = 1) (hb : d374837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373410, d374837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106263 q ha hb
    | true =>
      simp only [d373410, d374837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106264 q ha hb
  have h2 (q : Pattern) (ha : d373411 q = 1) (hb : d374838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373411, d374838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373411, d374838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373412 q = 1) (hb : d374839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373412, d374839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373412, d374839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373414 q = 1) (hb : d374841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373414, d374841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373414, d374841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373419 q = 1) (hb : d374846 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d373419, d374846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373419, d374846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373420 q = 1) (hb : d374847 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d373420, d374847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373420, d374847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106267 (p : Pattern) (ha : d373426 p = 1) (hb : d374853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373423 q = 1) (hb : d374850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373424 q = 1) (hb : d374851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373425 q = 1) (hb : d374852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373425, d374852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373425, d374852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373426 q = 1) (hb : d374853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373426, d374853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373426, d374853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106268 (p : Pattern) (ha : d373430 p = 1) (hb : d374857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373427 q = 1) (hb : d374854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373428 q = 1) (hb : d374855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373429 q = 1) (hb : d374856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373429, d374856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373429, d374856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373430 q = 1) (hb : d374857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373430, d374857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373430, d374857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106269 (p : Pattern) (ha : d373436 p = 1) (hb : d374863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373431 q = 1) (hb : d374858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106267 q ha hb
    | true =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106268 q ha hb
  have h2 (q : Pattern) (ha : d373432 q = 1) (hb : d374859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373432, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373432, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373433 q = 1) (hb : d374860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373433, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373433, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373434 q = 1) (hb : d374861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373434, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373434, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373435 q = 1) (hb : d374862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373435, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373435, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373436 q = 1) (hb : d374863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373436, d374863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373436, d374863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106270 (p : Pattern) (ha : d373439 p = 1) (hb : d374866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373423 q = 1) (hb : d374850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373424 q = 1) (hb : d374851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373425 q = 1) (hb : d374852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373425, d374852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373425, d374852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373439 q = 1) (hb : d374866 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373439, d374866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373439, d374866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106271 (p : Pattern) (ha : d373440 p = 1) (hb : d374867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373427 q = 1) (hb : d374854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373428 q = 1) (hb : d374855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373429 q = 1) (hb : d374856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373429, d374856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373429, d374856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373440 q = 1) (hb : d374867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373440, d374867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373440, d374867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106272 (p : Pattern) (ha : d373446 p = 1) (hb : d374873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373431 q = 1) (hb : d374858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106267 q ha hb
    | true =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106268 q ha hb
  have h2 (q : Pattern) (ha : d373432 q = 1) (hb : d374859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373432, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373432, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373433 q = 1) (hb : d374860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373433, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373433, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373434 q = 1) (hb : d374861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373434, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373434, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373435 q = 1) (hb : d374862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373435, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373435, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373441 q = 1) (hb : d374868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373441, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106270 q ha hb
    | true =>
      simp only [d373441, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106271 q ha hb
  have h7 (q : Pattern) (ha : d373442 q = 1) (hb : d374869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373442, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373442, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373443 q = 1) (hb : d374870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373443, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373443, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373444 q = 1) (hb : d374871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373444, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373444, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373445 q = 1) (hb : d374872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373445, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373445, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373446 q = 1) (hb : d374873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373446, d374873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373446, d374873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106273 (p : Pattern) (ha : d373451 p = 1) (hb : d374878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373423 q = 1) (hb : d374850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373424 q = 1) (hb : d374851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373450 q = 1) (hb : d374877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373450, d374877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373450, d374877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373451 q = 1) (hb : d374878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373451, d374878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373451, d374878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106274 (p : Pattern) (ha : d373453 p = 1) (hb : d374880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373427 q = 1) (hb : d374854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373428 q = 1) (hb : d374855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373452 q = 1) (hb : d374879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373452, d374879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373452, d374879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373453 q = 1) (hb : d374880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373453, d374880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373453, d374880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106275 (p : Pattern) (ha : d373460 p = 1) (hb : d374887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373423 q = 1) (hb : d374850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373458 q = 1) (hb : d374885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373458, d374885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373458, d374885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373459 q = 1) (hb : d374886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373459, d374886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373459, d374886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373460 q = 1) (hb : d374887 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373460, d374887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373460, d374887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106276 (p : Pattern) (ha : d373463 p = 1) (hb : d374890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373427 q = 1) (hb : d374854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373461 q = 1) (hb : d374888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373461, d374888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373461, d374888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373462 q = 1) (hb : d374889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373462, d374889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373462, d374889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373463 q = 1) (hb : d374890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373463, d374890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373463, d374890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106277 (p : Pattern) (ha : d373467 p = 1) (hb : d374461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341526 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d127 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d127 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d46865 q = 1) (hb : d341090 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d341090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d46865, d341090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d324332 q = 1) (hb : d373065 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d324332, d373065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324332, d373065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373467 q = 1) (hb : d374461 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d373467, d374461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373467, d374461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro106278 (p : Pattern) (ha : d373476 p = 1) (hb : d374896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373468 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373468, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106277 q ha hb
    | true =>
      simp only [d373468, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373469 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373469, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373469, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373470 q = 1) (hb : d374640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373470, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373470, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373471 q = 1) (hb : d374894 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373471, d374894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373471, d374894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373472 q = 1) (hb : d374895 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373472, d374895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373472, d374895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d373351 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d373352 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d373353 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373354 q = 1) (hb : d374640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373354, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373354, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373193 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373193, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106229 q hb ha
    | true =>
      simp only [d373193, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373194 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373194, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373194, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d373473 q = 1) (hb : d374464 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373473, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373473, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373474 q = 1) (hb : d374641 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373474, d374641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373474, d374641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373475 q = 1) (hb : d374642 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373475, d374642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373475, d374642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373476 q = 1) (hb : d374896 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373476, d374896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373476, d374896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106279 (p : Pattern) (ha : d373487 p = 1) (hb : d374901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373352 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d373353 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373354 q = 1) (hb : d374640 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373354, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373354, d374640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373067 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373067, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373067, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373068 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373068, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373068, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373193 q = 1) (hb : d374349 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373193, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106229 q hb ha
    | true =>
      simp only [d373193, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373194 q = 1) (hb : d374350 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373194, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373194, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373195 q = 1) (hb : d374464 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373195, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373195, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373355 q = 1) (hb : d374641 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373355, d374641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373355, d374641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373356 q = 1) (hb : d374642 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373356, d374642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373356, d374642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d373486 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d373487 q = 1) (hb : d374901 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373487, d374901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373487, d374901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro106280 (p : Pattern) (ha : d373502 p = 1) (hb : d374908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373477 q = 1) (hb : d374897 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373477, d374897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106278 q ha hb
    | true =>
      simp only [d373477, d374897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373478 q = 1) (hb : d374898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373478, d374898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373478, d374898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373479 q = 1) (hb : d374899 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373479, d374899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373479, d374899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373480 q = 1) (hb : d374900 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373480, d374900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373480, d374900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373488 q = 1) (hb : d374902 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373488, d374902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106279 q ha hb
    | true =>
      simp only [d373488, d374902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373489 q = 1) (hb : d374903 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373489, d374903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373489, d374903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373490 q = 1) (hb : d374904 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373490, d374904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373490, d374904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373491 q = 1) (hb : d374905 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373491, d374905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373491, d374905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373492 q = 1) (hb : d374906 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373492, d374906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373492, d374906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d373500 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d373384 q = 1) (hb : d374660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106259 q ha hb
    | true =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d373385 q = 1) (hb : d374661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d373386 q = 1) (hb : d374662 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373386, d374662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373386, d374662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373387 q = 1) (hb : d374663 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373387, d374663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373387, d374663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373501 q = 1) (hb : d374907 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373501, d374907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d373501, d374907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d373502 q = 1) (hb : d374908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373502, d374908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373502, d374908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro106281 (p : Pattern) (ha : d373509 p = 1) (hb : d374659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373351 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373352 q = 1) (hb : d374462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106192 q ha hb
    | true =>
      simp only [d373352, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373353 q = 1) (hb : d374463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373353, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d373370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373506 q = 1) (hb : d374656 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d373506, d374656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373506, d374656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373507 q = 1) (hb : d374657 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373507, d374657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373507, d374657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d373508 q = 1) (hb : d374658 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373508, d374658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373508, d374658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d46871 q = 1) (hb : d341093 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106147 q ha hb
    | true =>
      simp only [d46871, d341093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d341094 q = 1) (hb : d355776 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d341094, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h10 (q : Pattern) (ha : d356207 q = 1) (hb : d373371 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d356207, d373371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d356207, d373371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d373372 q = 1) (hb : d374648 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d373372, d374648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d373372, d374648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d373373 q = 1) (hb : d374649 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d373373, d374649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373373, d374649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h13 (q : Pattern) (ha : d373509 q = 1) (hb : d374659 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d373509, d374659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373509, d374659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro106282 (p : Pattern) (ha : d373515 p = 1) (hb : d374912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373510 q = 1) (hb : d374660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373510, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106281 q ha hb
    | true =>
      simp only [d373510, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373511 q = 1) (hb : d374661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373511, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373511, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373512 q = 1) (hb : d374662 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373512, d374662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373512, d374662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373513 q = 1) (hb : d374663 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373513, d374663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373513, d374663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373394 q = 1) (hb : d374826 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373394, d374826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373395 q = 1) (hb : d374827 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373395, d374827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373514 q = 1) (hb : d374828 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373514, d374828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373514, d374828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373404 q = 1) (hb : d374831 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373404, d374831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373404, d374831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373515 q = 1) (hb : d374912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373515, d374912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373515, d374912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106283 (p : Pattern) (ha : d373521 p = 1) (hb : d374918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373503 q = 1) (hb : d374909 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373503, d374909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106280 q ha hb
    | true =>
      simp only [d373503, d374909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106261 q ha hb
  have h2 (q : Pattern) (ha : d373504 q = 1) (hb : d374910 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373504, d374910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373504, d374910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373505 q = 1) (hb : d374911 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373505, d374911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373505, d374911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373516 q = 1) (hb : d374913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373516, d374913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106261 q ha hb
    | true =>
      simp only [d373516, d374913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106282 q ha hb
  have h5 (q : Pattern) (ha : d373517 q = 1) (hb : d374914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373517, d374914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373517, d374914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373518 q = 1) (hb : d374915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373518, d374915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373518, d374915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373519 q = 1) (hb : d374916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373519, d374916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373519, d374916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373406 q = 1) (hb : d374833 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373406, d374833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106261 q ha hb
    | true =>
      simp only [d373406, d374833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106263 q ha hb
  have h9 (q : Pattern) (ha : d373407 q = 1) (hb : d374834 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373407, d374834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373407, d374834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373408 q = 1) (hb : d374835 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373408, d374835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373408, d374835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373410 q = 1) (hb : d374837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373410, d374837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106263 q ha hb
    | true =>
      simp only [d373410, d374837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106264 q ha hb
  have h12 (q : Pattern) (ha : d373411 q = 1) (hb : d374838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373411, d374838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373411, d374838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373412 q = 1) (hb : d374839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373412, d374839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373412, d374839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373413 q = 1) (hb : d374840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373413, d374840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373413, d374840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d373520 q = 1) (hb : d374917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d373520, d374917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373520, d374917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d373521 q = 1) (hb : d374918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d373521, d374918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373521, d374918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro106284 (p : Pattern) (ha : d373527 p = 1) (hb : d374924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373522 q = 1) (hb : d374919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373522, d374919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106283 q ha hb
    | true =>
      simp only [d373522, d374919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373523 q = 1) (hb : d374920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373523, d374920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373523, d374920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373524 q = 1) (hb : d374921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373524, d374921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373524, d374921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373525 q = 1) (hb : d374922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373525, d374922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373525, d374922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373526 q = 1) (hb : d374923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373526, d374923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373526, d374923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373527 q = 1) (hb : d374924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373527, d374924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373527, d374924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106285 (p : Pattern) (ha : d373533 p = 1) (hb : d374930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373530 q = 1) (hb : d374927 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373530, d374927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373530, d374927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373531 q = 1) (hb : d374928 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373531, d374928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373531, d374928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373532 q = 1) (hb : d374929 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373532, d374929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373532, d374929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373533 q = 1) (hb : d374930 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373533, d374930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373533, d374930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106286 (p : Pattern) (ha : d373539 p = 1) (hb : d374936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373454 q = 1) (hb : d374881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373454, d374881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106273 q ha hb
    | true =>
      simp only [d373454, d374881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106274 q ha hb
  have h2 (q : Pattern) (ha : d373455 q = 1) (hb : d374882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373455, d374882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373455, d374882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373456 q = 1) (hb : d374883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373456, d374883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373456, d374883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373457 q = 1) (hb : d374884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373457, d374884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373457, d374884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373464 q = 1) (hb : d374891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373464, d374891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106275 q ha hb
    | true =>
      simp only [d373464, d374891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106276 q ha hb
  have h6 (q : Pattern) (ha : d373465 q = 1) (hb : d374892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373465, d374892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373465, d374892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373466 q = 1) (hb : d374893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373466, d374893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373466, d374893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373528 q = 1) (hb : d374925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373528, d374925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106284 q ha hb
    | true =>
      simp only [d373528, d374925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106267 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d373431 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d373529 q = 1) (hb : d374926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373529, d374926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373529, d374926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d373534 q = 1) (hb : d374931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373534, d374931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106285 q ha hb
    | true =>
      simp only [d373534, d374931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d373535 q = 1) (hb : d374932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373535, d374932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373535, d374932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d373536 q = 1) (hb : d374933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373536, d374933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373536, d374933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373537 q = 1) (hb : d374934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373537, d374934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373537, d374934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d373538 q = 1) (hb : d374935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373538, d374935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373538, d374935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d373539 q = 1) (hb : d374936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373539, d374936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373539, d374936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro106287 (p : Pattern) (ha : d373540 p = 1) (hb : d374937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373423 q = 1) (hb : d374850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373424 q = 1) (hb : d374851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373424, d374851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373450 q = 1) (hb : d374877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373450, d374877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373450, d374877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373540 q = 1) (hb : d374937 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373540, d374937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373540, d374937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106288 (p : Pattern) (ha : d373541 p = 1) (hb : d374938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373427 q = 1) (hb : d374854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373428 q = 1) (hb : d374855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373428, d374855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373452 q = 1) (hb : d374879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373452, d374879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373452, d374879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373541 q = 1) (hb : d374938 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373541, d374938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373541, d374938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106289 (p : Pattern) (ha : d373546 p = 1) (hb : d374943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373423 q = 1) (hb : d374850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373423, d374850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373458 q = 1) (hb : d374885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373458, d374885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373458, d374885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373459 q = 1) (hb : d374886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373459, d374886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373459, d374886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373546 q = 1) (hb : d374943 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373546, d374943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373546, d374943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106290 (p : Pattern) (ha : d373547 p = 1) (hb : d374944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373421 q = 1) (hb : d374848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106266 q ha hb
    | true =>
      simp only [d373421, d374848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373422 q = 1) (hb : d374849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373422, d374849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373427 q = 1) (hb : d374854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373427, d374854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373461 q = 1) (hb : d374888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373461, d374888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373461, d374888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373462 q = 1) (hb : d374889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373462, d374889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373462, d374889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373547 q = 1) (hb : d374944 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373547, d374944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373547, d374944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106291 (p : Pattern) (ha : d373551 p = 1) (hb : d374948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373522 q = 1) (hb : d374919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373522, d374919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106283 q ha hb
    | true =>
      simp only [d373522, d374919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373523 q = 1) (hb : d374920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373523, d374920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373523, d374920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373524 q = 1) (hb : d374921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373524, d374921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373524, d374921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373525 q = 1) (hb : d374922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373525, d374922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373525, d374922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373526 q = 1) (hb : d374923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373526, d374923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373526, d374923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373551 q = 1) (hb : d374948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373551, d374948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373551, d374948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106292 (p : Pattern) (ha : d373554 p = 1) (hb : d374951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373417 q = 1) (hb : d374844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106265 q ha hb
    | true =>
      simp only [d373417, d374844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373418 q = 1) (hb : d374845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373418, d374845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373530 q = 1) (hb : d374927 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373530, d374927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373530, d374927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373531 q = 1) (hb : d374928 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373531, d374928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373531, d374928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373532 q = 1) (hb : d374929 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373532, d374929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373532, d374929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373554 q = 1) (hb : d374951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373554, d374951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373554, d374951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106293 (p : Pattern) (ha : d373560 p = 1) (hb : d374957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373454 q = 1) (hb : d374881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373454, d374881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106273 q ha hb
    | true =>
      simp only [d373454, d374881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106274 q ha hb
  have h2 (q : Pattern) (ha : d373455 q = 1) (hb : d374882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373455, d374882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373455, d374882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373456 q = 1) (hb : d374883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373456, d374883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373456, d374883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373457 q = 1) (hb : d374884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373457, d374884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373457, d374884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373464 q = 1) (hb : d374891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373464, d374891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106275 q ha hb
    | true =>
      simp only [d373464, d374891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106276 q ha hb
  have h6 (q : Pattern) (ha : d373465 q = 1) (hb : d374892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373465, d374892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373465, d374892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373466 q = 1) (hb : d374893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373466, d374893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373466, d374893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373528 q = 1) (hb : d374925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373528, d374925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106284 q ha hb
    | true =>
      simp only [d373528, d374925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106267 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d373431 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d373529 q = 1) (hb : d374926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373529, d374926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373529, d374926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d373534 q = 1) (hb : d374931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373534, d374931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106285 q ha hb
    | true =>
      simp only [d373534, d374931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d373535 q = 1) (hb : d374932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373535, d374932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373535, d374932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d373536 q = 1) (hb : d374933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373536, d374933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373536, d374933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373537 q = 1) (hb : d374934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373537, d374934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373537, d374934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d373538 q = 1) (hb : d374935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373538, d374935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373538, d374935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d373542 q = 1) (hb : d374939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373542, d374939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106287 q ha hb
    | true =>
      simp only [d373542, d374939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106288 q ha hb
  have h17 (q : Pattern) (ha : d373543 q = 1) (hb : d374940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373543, d374940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373543, d374940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d373544 q = 1) (hb : d374941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373544, d374941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373544, d374941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d373545 q = 1) (hb : d374942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373545, d374942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373545, d374942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d373548 q = 1) (hb : d374945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373548, d374945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106289 q ha hb
    | true =>
      simp only [d373548, d374945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106290 q ha hb
  have h21 (q : Pattern) (ha : d373549 q = 1) (hb : d374946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373549, d374946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373549, d374946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d373550 q = 1) (hb : d374947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373550, d374947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d373550, d374947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d373552 q = 1) (hb : d374949 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373552, d374949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106291 q ha hb
    | true =>
      simp only [d373552, d374949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106270 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d373441 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d373553 q = 1) (hb : d374950 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373553, d374950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d373553, d374950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d373555 q = 1) (hb : d374952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373555, d374952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106292 q ha hb
    | true =>
      simp only [d373555, d374952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d373556 q = 1) (hb : d374953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373556, d374953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d373556, d374953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d373557 q = 1) (hb : d374954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373557, d374954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d373557, d374954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d373558 q = 1) (hb : d374955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373558, d374955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d373558, d374955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d373559 q = 1) (hb : d374956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373559, d374956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d373559, d374956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d373560 q = 1) (hb : d374957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373560, d374957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373560, d374957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro106294 (p : Pattern) (ha : d373567 p = 1) (hb : d374964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373431 q = 1) (hb : d374858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106267 q ha hb
    | true =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106268 q ha hb
  have h2 (q : Pattern) (ha : d373432 q = 1) (hb : d374859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373432, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373432, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373433 q = 1) (hb : d374860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373433, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373433, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373434 q = 1) (hb : d374861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373434, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373434, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373435 q = 1) (hb : d374862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373435, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373435, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373562 q = 1) (hb : d374959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373562, d374959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106268 q ha hb
    | true =>
      simp only [d373562, d374959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373563 q = 1) (hb : d374960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373563, d374960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373563, d374960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373564 q = 1) (hb : d374961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373564, d374961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373564, d374961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373565 q = 1) (hb : d374962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373565, d374962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373565, d374962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373566 q = 1) (hb : d374963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373566, d374963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373566, d374963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373567 q = 1) (hb : d374964 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373567, d374964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373567, d374964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106295 (p : Pattern) (ha : d373573 p = 1) (hb : d374970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373562 q = 1) (hb : d374959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373562, d374959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106268 q ha hb
    | true =>
      simp only [d373562, d374959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373563 q = 1) (hb : d374960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373563, d374960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373563, d374960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373564 q = 1) (hb : d374961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373564, d374961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373564, d374961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373565 q = 1) (hb : d374962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373565, d374962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373565, d374962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373566 q = 1) (hb : d374963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373566, d374963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373566, d374963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373568 q = 1) (hb : d374965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373568, d374965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106271 q ha hb
    | true =>
      simp only [d373568, d374965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373569 q = 1) (hb : d374966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373569, d374966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373569, d374966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373570 q = 1) (hb : d374967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373570, d374967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373570, d374967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373571 q = 1) (hb : d374968 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373571, d374968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373571, d374968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373572 q = 1) (hb : d374969 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373572, d374969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373572, d374969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373573 q = 1) (hb : d374970 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373573, d374970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373573, d374970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106296 (p : Pattern) (ha : d373580 p = 1) (hb : d374977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373552 q = 1) (hb : d374949 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373552, d374949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106291 q ha hb
    | true =>
      simp only [d373552, d374949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106270 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373553 q = 1) (hb : d374950 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373553, d374950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373553, d374950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d373555 q = 1) (hb : d374952 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373555, d374952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106292 q ha hb
    | true =>
      simp only [d373555, d374952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373556 q = 1) (hb : d374953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373556, d374953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373556, d374953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373557 q = 1) (hb : d374954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373557, d374954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373557, d374954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373578 q = 1) (hb : d374975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373578, d374975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373578, d374975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373579 q = 1) (hb : d374976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373579, d374976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373579, d374976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373580 q = 1) (hb : d374977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373580, d374977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373580, d374977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro106297 (p : Pattern) (ha : d373582 p = 1) (hb : d374979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373568 q = 1) (hb : d374965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373568, d374965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106271 q ha hb
    | true =>
      simp only [d373568, d374965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373569 q = 1) (hb : d374966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373569, d374966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373569, d374966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373570 q = 1) (hb : d374967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373570, d374967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373570, d374967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373571 q = 1) (hb : d374968 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373571, d374968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373571, d374968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373572 q = 1) (hb : d374969 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373572, d374969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373572, d374969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373582 q = 1) (hb : d374979 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373582, d374979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373582, d374979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106298 (p : Pattern) (ha : d373606 p = 1) (hb : d374995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373588 q = 1) (hb : d374985 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373588, d374985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373588, d374985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106278 q ha hb
  have h2 (q : Pattern) (ha : d373477 q = 1) (hb : d374897 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373477, d374897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106278 q ha hb
    | true =>
      simp only [d373477, d374897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373589 q = 1) (hb : d374986 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373589, d374986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373589, d374986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373478 q = 1) (hb : d374898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373478, d374898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373478, d374898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373590 q = 1) (hb : d374987 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373590, d374987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373590, d374987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373591 q = 1) (hb : d374988 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373591, d374988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373591, d374988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373592 q = 1) (hb : d374989 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373592, d374989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373592, d374989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106279 q ha hb
  have h8 (q : Pattern) (ha : d373488 q = 1) (hb : d374902 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373488, d374902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106279 q ha hb
    | true =>
      simp only [d373488, d374902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373593 q = 1) (hb : d374990 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373593, d374990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373593, d374990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373489 q = 1) (hb : d374903 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373489, d374903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373489, d374903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373594 q = 1) (hb : d374991 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373594, d374991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373594, d374991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d373595 q = 1) (hb : d374992 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373595, d374992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373595, d374992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d373596 q = 1) (hb : d374993 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373596, d374993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373596, d374993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d373600 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d373601 q = 1) (hb : d374751 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373601, d374751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373601, d374751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106259 q ha hb
  have h16 (q : Pattern) (ha : d373384 q = 1) (hb : d374660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106259 q ha hb
    | true =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d373602 q = 1) (hb : d374752 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373602, d374752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373602, d374752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d373385 q = 1) (hb : d374661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d373603 q = 1) (hb : d374753 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373603, d374753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373603, d374753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d373604 q = 1) (hb : d374754 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373604, d374754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d373604, d374754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d373605 q = 1) (hb : d374994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373605, d374994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d373605, d374994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d373606 q = 1) (hb : d374995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373606, d374995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373606, d374995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro106299 (p : Pattern) (ha : d373621 p = 1) (hb : d375001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373607 q = 1) (hb : d374742 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373607, d374742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373607, d374742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106257 q ha hb
  have h2 (q : Pattern) (ha : d373363 q = 1) (hb : d374644 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373363, d374644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106257 q ha hb
    | true =>
      simp only [d373363, d374644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373608 q = 1) (hb : d374743 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373608, d374743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373608, d374743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373364 q = 1) (hb : d374645 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373364, d374645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373364, d374645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373609 q = 1) (hb : d374744 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373609, d374744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373609, d374744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373610 q = 1) (hb : d374745 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373610, d374745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373610, d374745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373611 q = 1) (hb : d374746 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373611, d374746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373611, d374746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106258 q ha hb
  have h8 (q : Pattern) (ha : d373375 q = 1) (hb : d374651 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373375, d374651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106258 q ha hb
    | true =>
      simp only [d373375, d374651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373612 q = 1) (hb : d374747 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373612, d374747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373612, d374747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373376 q = 1) (hb : d374652 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373376, d374652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373376, d374652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373613 q = 1) (hb : d374748 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373613, d374748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373613, d374748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d373614 q = 1) (hb : d374749 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373614, d374749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373614, d374749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d373615 q = 1) (hb : d374750 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373615, d374750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373615, d374750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373601 q = 1) (hb : d374751 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373601, d374751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373601, d374751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106259 q ha hb
  have h15 (q : Pattern) (ha : d373384 q = 1) (hb : d374660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106259 q ha hb
    | true =>
      simp only [d373384, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d373602 q = 1) (hb : d374752 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373602, d374752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d373602, d374752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d373385 q = 1) (hb : d374661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373385, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d373603 q = 1) (hb : d374753 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373603, d374753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373603, d374753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d373604 q = 1) (hb : d374754 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373604, d374754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d373604, d374754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d373616 q = 1) (hb : d374996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
  have h21 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d373617 q = 1) (hb : d374997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d373618 q = 1) (hb : d374998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d373619 q = 1) (hb : d374999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d373620 q = 1) (hb : d375000 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373620, d375000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d373620, d375000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d373621 q = 1) (hb : d375001 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373621, d375001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373621, d375001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro106300 (p : Pattern) (ha : d373631 p = 1) (hb : d375006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373625 q = 1) (hb : d374751 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373625, d374751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373625, d374751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106281 q ha hb
  have h2 (q : Pattern) (ha : d373510 q = 1) (hb : d374660 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373510, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106281 q ha hb
    | true =>
      simp only [d373510, d374660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373626 q = 1) (hb : d374752 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373626, d374752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373626, d374752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373511 q = 1) (hb : d374661 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373511, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373511, d374661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373627 q = 1) (hb : d374753 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373627, d374753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373627, d374753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373628 q = 1) (hb : d374754 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373628, d374754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373628, d374754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373616 q = 1) (hb : d374996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
  have h8 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373617 q = 1) (hb : d374997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373618 q = 1) (hb : d374998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d373619 q = 1) (hb : d374999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d373629 q = 1) (hb : d375000 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373629, d375000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373629, d375000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373630 q = 1) (hb : d375005 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373630, d375005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d373630, d375005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373631 q = 1) (hb : d375006 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373631, d375006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373631, d375006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106301 (p : Pattern) (ha : d373641 p = 1) (hb : d375012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373636 q = 1) (hb : d374539 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373636, d374539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373636, d374539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106262 q ha hb
  have h2 (q : Pattern) (ha : d373399 q = 1) (hb : d374468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373399, d374468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106262 q ha hb
    | true =>
      simp only [d373399, d374468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373637 q = 1) (hb : d374540 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373637, d374540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373637, d374540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373400 q = 1) (hb : d374469 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373400, d374469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373400, d374469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373638 q = 1) (hb : d374541 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373638, d374541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373638, d374541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373639 q = 1) (hb : d374542 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373639, d374542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373639, d374542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373616 q = 1) (hb : d374996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
  have h8 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373617 q = 1) (hb : d374997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d373618 q = 1) (hb : d374998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d373619 q = 1) (hb : d374999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d373640 q = 1) (hb : d375011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373640, d375011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373640, d375011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373630 q = 1) (hb : d375005 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373630, d375005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d373630, d375005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373641 q = 1) (hb : d375012 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373641, d375012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373641, d375012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106302 (p : Pattern) (ha : d373645 p = 1) (hb : d375016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373616 q = 1) (hb : d374996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373616, d374996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
  have h2 (q : Pattern) (ha : d373392 q = 1) (hb : d374824 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106260 q ha hb
    | true =>
      simp only [d373392, d374824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373617 q = 1) (hb : d374997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373617, d374997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373393 q = 1) (hb : d374825 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373393, d374825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373618 q = 1) (hb : d374998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373618, d374998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373619 q = 1) (hb : d374999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373619, d374999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373630 q = 1) (hb : d375005 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d373630, d375005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373630, d375005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373645 q = 1) (hb : d375016 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d373645, d375016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373645, d375016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106303 (p : Pattern) (ha : d373651 p = 1) (hb : d375022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373622 q = 1) (hb : d375002 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373622, d375002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106298 q ha hb
    | true =>
      simp only [d373622, d375002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106299 q ha hb
  have h2 (q : Pattern) (ha : d373623 q = 1) (hb : d375003 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373623, d375003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373623, d375003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373624 q = 1) (hb : d375004 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373624, d375004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373624, d375004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373632 q = 1) (hb : d375007 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373632, d375007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106299 q ha hb
    | true =>
      simp only [d373632, d375007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106300 q ha hb
  have h5 (q : Pattern) (ha : d373633 q = 1) (hb : d375008 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373633, d375008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373633, d375008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373634 q = 1) (hb : d375009 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373634, d375009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373634, d375009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373635 q = 1) (hb : d375010 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373635, d375010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373635, d375010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373642 q = 1) (hb : d375013 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373642, d375013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106299 q ha hb
    | true =>
      simp only [d373642, d375013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106301 q ha hb
  have h9 (q : Pattern) (ha : d373643 q = 1) (hb : d375014 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373643, d375014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373643, d375014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373644 q = 1) (hb : d375015 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373644, d375015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373644, d375015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373646 q = 1) (hb : d375017 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373646, d375017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106301 q ha hb
    | true =>
      simp only [d373646, d375017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106302 q ha hb
  have h12 (q : Pattern) (ha : d373647 q = 1) (hb : d375018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373647, d375018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373647, d375018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373648 q = 1) (hb : d375019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373648, d375019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373648, d375019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373649 q = 1) (hb : d375020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373649, d375020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373649, d375020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d373650 q = 1) (hb : d375021 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d373650, d375021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373650, d375021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d373651 q = 1) (hb : d375022 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d373651, d375022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373651, d375022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro106304 (p : Pattern) (ha : d373656 p = 1) (hb : d375027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373642 q = 1) (hb : d375013 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373642, d375013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106299 q ha hb
    | true =>
      simp only [d373642, d375013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106301 q ha hb
  have h2 (q : Pattern) (ha : d373643 q = 1) (hb : d375014 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373643, d375014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373643, d375014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373644 q = 1) (hb : d375015 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373644, d375015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373644, d375015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373646 q = 1) (hb : d375017 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373646, d375017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106301 q ha hb
    | true =>
      simp only [d373646, d375017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106302 q ha hb
  have h5 (q : Pattern) (ha : d373647 q = 1) (hb : d375018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373647, d375018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373647, d375018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373648 q = 1) (hb : d375019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373648, d375019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373648, d375019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373649 q = 1) (hb : d375020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373649, d375020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373649, d375020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373654 q = 1) (hb : d375025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373654, d375025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373654, d375025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d373655 q = 1) (hb : d375026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d373655, d375026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373655, d375026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373656 q = 1) (hb : d375027 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d373656, d375027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373656, d375027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro106305 (p : Pattern) (ha : d373662 p = 1) (hb : d375033 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373652 q = 1) (hb : d375023 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373652, d375023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106303 q ha hb
    | true =>
      simp only [d373652, d375023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373653 q = 1) (hb : d375024 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373653, d375024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373653, d375024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373657 q = 1) (hb : d375028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373657, d375028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106304 q ha hb
    | true =>
      simp only [d373657, d375028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373658 q = 1) (hb : d375029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373658, d375029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373658, d375029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373659 q = 1) (hb : d375030 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373659, d375030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373659, d375030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373660 q = 1) (hb : d375031 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373660, d375031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373660, d375031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373661 q = 1) (hb : d375032 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373661, d375032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373661, d375032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373662 q = 1) (hb : d375033 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373662, d375033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373662, d375033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106306 (p : Pattern) (ha : d373664 p = 1) (hb : d375035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373646 q = 1) (hb : d375017 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d373646, d375017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106301 q ha hb
    | true =>
      simp only [d373646, d375017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106302 q ha hb
  have h2 (q : Pattern) (ha : d373647 q = 1) (hb : d375018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d373647, d375018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373647, d375018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373648 q = 1) (hb : d375019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d373648, d375019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373648, d375019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373654 q = 1) (hb : d375025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d373654, d375025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373654, d375025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373663 q = 1) (hb : d375034 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d373663, d375034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373663, d375034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373664 q = 1) (hb : d375035 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d373664, d375035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373664, d375035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106307 (p : Pattern) (ha : d373670 p = 1) (hb : d375041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373657 q = 1) (hb : d375028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373657, d375028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106304 q ha hb
    | true =>
      simp only [d373657, d375028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373658 q = 1) (hb : d375029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373658, d375029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373658, d375029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373665 q = 1) (hb : d375036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373665, d375036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106306 q ha hb
    | true =>
      simp only [d373665, d375036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373666 q = 1) (hb : d375037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373666, d375037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373666, d375037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373667 q = 1) (hb : d375038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373667, d375038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373667, d375038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373668 q = 1) (hb : d375039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373668, d375039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373668, d375039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d373669 q = 1) (hb : d375040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373669, d375040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373669, d375040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d373670 q = 1) (hb : d375041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373670, d375041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373670, d375041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro106308 (p : Pattern) (ha : d373681 p = 1) (hb : d375047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373657 q = 1) (hb : d375028 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373657, d375028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106304 q ha hb
    | true =>
      simp only [d373657, d375028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373658 q = 1) (hb : d375029 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373658, d375029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373658, d375029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373678 q = 1) (hb : d375044 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373678, d375044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373678, d375044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373679 q = 1) (hb : d375045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373679, d375045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373679, d375045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373680 q = 1) (hb : d375046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373680, d375046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373680, d375046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373681 q = 1) (hb : d375047 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373681, d375047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373681, d375047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106309 (p : Pattern) (ha : d373687 p = 1) (hb : d375053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373671 q = 1) (hb : d375042 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373671, d375042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106305 q ha hb
    | true =>
      simp only [d373671, d375042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106307 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373676 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373677 q = 1) (hb : d375043 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373677, d375043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373677, d375043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d373682 q = 1) (hb : d375048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373682, d375048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106308 q ha hb
    | true =>
      simp only [d373682, d375048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373683 q = 1) (hb : d375049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373683, d375049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373683, d375049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373684 q = 1) (hb : d375050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373684, d375050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373684, d375050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373685 q = 1) (hb : d375051 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373685, d375051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373685, d375051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373686 q = 1) (hb : d375052 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373686, d375052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373686, d375052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373687 q = 1) (hb : d375053 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373687, d375053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373687, d375053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro106310 (p : Pattern) (ha : d373675 p = 1) (hb : d375058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373665 q = 1) (hb : d375036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d373665, d375036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106306 q ha hb
    | true =>
      simp only [d373665, d375036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373666 q = 1) (hb : d375037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d373666, d375037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373666, d375037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373672 q = 1) (hb : d375055 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d373672, d375055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373672, d375055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373673 q = 1) (hb : d375056 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d373673, d375056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373673, d375056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373674 q = 1) (hb : d375057 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d373674, d375057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373674, d375057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d373675 q = 1) (hb : d375058 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d373675, d375058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373675, d375058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106311 (p : Pattern) (ha : d373694 p = 1) (hb : d375064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373689 q = 1) (hb : d375059 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373689, d375059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106310 q ha hb
    | true =>
      simp only [d373689, d375059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d373690 q = 1) (hb : d375060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373690, d375060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373690, d375060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373691 q = 1) (hb : d375061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373691, d375061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373691, d375061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d373692 q = 1) (hb : d375062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373692, d375062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373692, d375062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373693 q = 1) (hb : d375063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373693, d375063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373693, d375063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373694 q = 1) (hb : d375064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373694, d375064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373694, d375064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106312 (p : Pattern) (ha : d373700 p = 1) (hb : d375070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373437 q = 1) (hb : d374864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373437, d374864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373437, d374864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106269 q ha hb
  have h2 (q : Pattern) (ha : d373438 q = 1) (hb : d374865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373438, d374865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373438, d374865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d373447 q = 1) (hb : d374874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373447, d374874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106269 q ha hb
    | true =>
      simp only [d373447, d374874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106272 q ha hb
  have h4 (q : Pattern) (ha : d373448 q = 1) (hb : d374875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373448, d374875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373448, d374875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d373449 q = 1) (hb : d374876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373449, d374876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d373449, d374876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373561 q = 1) (hb : d374958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373561, d374958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106286 q ha hb
    | true =>
      simp only [d373561, d374958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106293 q ha hb
  have h7 (q : Pattern) (ha : d373574 q = 1) (hb : d374971 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373574, d374971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106294 q ha hb
    | true =>
      simp only [d373574, d374971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106295 q ha hb
  have h8 (q : Pattern) (ha : d373575 q = 1) (hb : d374972 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373575, d374972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373575, d374972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373576 q = 1) (hb : d374973 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373576, d374973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373576, d374973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d373577 q = 1) (hb : d374974 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373577, d374974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373577, d374974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d373581 q = 1) (hb : d374978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373581, d374978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373581, d374978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106296 q ha hb
  have h12 (q : Pattern) (ha : d373583 q = 1) (hb : d374980 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373583, d374980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373583, d374980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106297 q ha hb
  have h13 (q : Pattern) (ha : d373584 q = 1) (hb : d374981 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373584, d374981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d373584, d374981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d373585 q = 1) (hb : d374982 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373585, d374982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373585, d374982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d373586 q = 1) (hb : d374983 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373586, d374983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d373586, d374983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d373587 q = 1) (hb : d374984 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373587, d374984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373587, d374984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d373688 q = 1) (hb : d375054 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373688, d375054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373688, d375054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106309 q ha hb
  have h18 (q : Pattern) (ha : d373695 q = 1) (hb : d375065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373695, d375065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373695, d375065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106311 q ha hb
  have h19 (q : Pattern) (ha : d373696 q = 1) (hb : d375066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373696, d375066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373696, d375066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d373697 q = 1) (hb : d375067 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373697, d375067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d373697, d375067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d373698 q = 1) (hb : d375068 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373698, d375068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d373698, d375068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d373699 q = 1) (hb : d375069 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373699, d375069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d373699, d375069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d373700 q = 1) (hb : d375070 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d373700, d375070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373700, d375070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro106313 (p : Pattern) (ha : d373706 p = 1) (hb : d375076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373701 q = 1) (hb : d375071 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d373701, d375071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373701, d375071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106312 q ha hb
  have h2 (q : Pattern) (ha : d373702 q = 1) (hb : d375072 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d373702, d375072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373702, d375072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373703 q = 1) (hb : d375073 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d373703, d375073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373703, d375073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373704 q = 1) (hb : d375074 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d373704, d375074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373704, d375074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373705 q = 1) (hb : d375075 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d373705, d375075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373705, d375075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373706 q = 1) (hb : d375076 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d373706, d375076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373706, d375076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106314 (p : Pattern) (ha : d374306 p = 1) (hb : d375082 p = 1) : d375126 p = 1 := by
  have h0 (q : Pattern) (ha : d373152 q = 1) (hb : d374586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d373152, d374586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106182 q ha hb
    | true =>
      simp only [d373152, d374586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106210 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373349 q = 1) (hb : d374821 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d373349, d374821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373349, d374821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106256 q ha hb
  have h3 (q : Pattern) (ha : d373350 q = 1) (hb : d374822 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d373350, d374822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d373350, d374822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373707 q = 1) (hb : d375077 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d373707, d375077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373707, d375077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106313 q ha hb
  have h5 (q : Pattern) (ha : d373708 q = 1) (hb : d375078 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d373708, d375078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373708, d375078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373709 q = 1) (hb : d375079 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d373709, d375079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373709, d375079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d374062 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d374063 q = 1) (hb : d375080 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d374063, d375080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d374063, d375080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d321724 q = 1) (hb : d374304 q = 1) : d321724 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d374305 q = 1) (hb : d375081 q = 1) : d375125 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d374305, d375081, d375125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d374305, d375081, d375125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d374306 q = 1) (hb : d375082 q = 1) : d375126 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d374306, d375082, d375126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d374306, d375082, d375126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h11 p ha hb
theorem andIntro106315 (p : Pattern) (ha : d374312 p = 1) (hb : d375088 p = 1) : d375132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374307 q = 1) (hb : d375083 q = 1) : d375127 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d374307, d375083, d375127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106314 q ha hb
    | true =>
      simp only [d374307, d375083, d375127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374308 q = 1) (hb : d375084 q = 1) : d375128 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d374308, d375084, d375128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374308, d375084, d375128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374309 q = 1) (hb : d375085 q = 1) : d375129 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d374309, d375085, d375129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374309, d375085, d375129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374310 q = 1) (hb : d375086 q = 1) : d375130 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d374310, d375086, d375130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374310, d375086, d375130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374311 q = 1) (hb : d375087 q = 1) : d375131 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d374311, d375087, d375131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374311, d375087, d375131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374312 q = 1) (hb : d375088 q = 1) : d375132 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d374312, d375088, d375132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374312, d375088, d375132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106316 (p : Pattern) (ha : d374318 p = 1) (hb : d375094 p = 1) : d375138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374313 q = 1) (hb : d375089 q = 1) : d375133 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d374313, d375089, d375133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106315 q ha hb
    | true =>
      simp only [d374313, d375089, d375133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374314 q = 1) (hb : d375090 q = 1) : d375134 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d374314, d375090, d375134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374314, d375090, d375134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374315 q = 1) (hb : d375091 q = 1) : d375135 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d374315, d375091, d375135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374315, d375091, d375135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374316 q = 1) (hb : d375092 q = 1) : d375136 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d374316, d375092, d375136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374316, d375092, d375136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374317 q = 1) (hb : d375093 q = 1) : d375137 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d374317, d375093, d375137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374317, d375093, d375137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374318 q = 1) (hb : d375094 q = 1) : d375138 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d374318, d375094, d375138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374318, d375094, d375138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106317 (p : Pattern) (ha : d374324 p = 1) (hb : d375100 p = 1) : d375144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374319 q = 1) (hb : d375095 q = 1) : d375139 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d374319, d375095, d375139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106316 q ha hb
    | true =>
      simp only [d374319, d375095, d375139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374320 q = 1) (hb : d375096 q = 1) : d375140 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d374320, d375096, d375140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374320, d375096, d375140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374321 q = 1) (hb : d375097 q = 1) : d375141 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d374321, d375097, d375141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374321, d375097, d375141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374322 q = 1) (hb : d375098 q = 1) : d375142 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d374322, d375098, d375142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374322, d375098, d375142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374323 q = 1) (hb : d375099 q = 1) : d375143 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d374323, d375099, d375143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374323, d375099, d375143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374324 q = 1) (hb : d375100 q = 1) : d375144 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d374324, d375100, d375144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374324, d375100, d375144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106318 (p : Pattern) (ha : d374330 p = 1) (hb : d375106 p = 1) : d375150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374325 q = 1) (hb : d375101 q = 1) : d375145 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d374325, d375101, d375145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106317 q ha hb
    | true =>
      simp only [d374325, d375101, d375145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374326 q = 1) (hb : d375102 q = 1) : d375146 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d374326, d375102, d375146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374326, d375102, d375146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374327 q = 1) (hb : d375103 q = 1) : d375147 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d374327, d375103, d375147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374327, d375103, d375147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374328 q = 1) (hb : d375104 q = 1) : d375148 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d374328, d375104, d375148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374328, d375104, d375148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374329 q = 1) (hb : d375105 q = 1) : d375149 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d374329, d375105, d375149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374329, d375105, d375149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374330 q = 1) (hb : d375106 q = 1) : d375150 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d374330, d375106, d375150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374330, d375106, d375150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106319 (p : Pattern) (ha : d374336 p = 1) (hb : d375112 p = 1) : d375156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374331 q = 1) (hb : d375107 q = 1) : d375151 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d374331, d375107, d375151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106318 q ha hb
    | true =>
      simp only [d374331, d375107, d375151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374332 q = 1) (hb : d375108 q = 1) : d375152 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d374332, d375108, d375152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374332, d375108, d375152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374333 q = 1) (hb : d375109 q = 1) : d375153 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d374333, d375109, d375153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374333, d375109, d375153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374334 q = 1) (hb : d375110 q = 1) : d375154 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d374334, d375110, d375154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374334, d375110, d375154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374335 q = 1) (hb : d375111 q = 1) : d375155 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d374335, d375111, d375155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374335, d375111, d375155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374336 q = 1) (hb : d375112 q = 1) : d375156 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d374336, d375112, d375156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374336, d375112, d375156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106320 (p : Pattern) (ha : d374342 p = 1) (hb : d375118 p = 1) : d375162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374337 q = 1) (hb : d375113 q = 1) : d375157 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d374337, d375113, d375157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106319 q ha hb
    | true =>
      simp only [d374337, d375113, d375157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374338 q = 1) (hb : d375114 q = 1) : d375158 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d374338, d375114, d375158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374338, d375114, d375158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374339 q = 1) (hb : d375115 q = 1) : d375159 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d374339, d375115, d375159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374339, d375115, d375159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374340 q = 1) (hb : d375116 q = 1) : d375160 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d374340, d375116, d375160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374340, d375116, d375160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374341 q = 1) (hb : d375117 q = 1) : d375161 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d374341, d375117, d375161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374341, d375117, d375161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374342 q = 1) (hb : d375118 q = 1) : d375162 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d374342, d375118, d375162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374342, d375118, d375162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106321 (p : Pattern) (ha : d374348 p = 1) (hb : d375124 p = 1) : d375168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374343 q = 1) (hb : d375119 q = 1) : d375163 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d374343, d375119, d375163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106320 q ha hb
    | true =>
      simp only [d374343, d375119, d375163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374344 q = 1) (hb : d375120 q = 1) : d375164 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d374344, d375120, d375164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374344, d375120, d375164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374345 q = 1) (hb : d375121 q = 1) : d375165 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d374345, d375121, d375165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374345, d375121, d375165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374346 q = 1) (hb : d375122 q = 1) : d375166 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d374346, d375122, d375166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374346, d375122, d375166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374347 q = 1) (hb : d375123 q = 1) : d375167 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d374347, d375123, d375167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374347, d375123, d375167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374348 q = 1) (hb : d375124 q = 1) : d375168 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d374348, d375124, d375168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374348, d375124, d375168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106322 (p : Pattern) (ha : d46864 p = 1) (hb : d321880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46532 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105887 q ha hb
    | true =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105888 q ha hb
  have h2 (q : Pattern) (ha : d46533 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46534 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46535 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46536 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro106323 (p : Pattern) (ha : d46864 p = 1) (hb : d321891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d321886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105924 q hb ha
    | true =>
      simp only [d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105896 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d321887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d321888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d321889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d321890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106324 (p : Pattern) (ha : d46864 p = 1) (hb : d321897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105886 q ha hb
    | true =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105889 q ha hb
  have h2 (q : Pattern) (ha : d46539 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d321878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d321879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d321881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106322 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d321883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d321884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d321885 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d321892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106323 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d321893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d321894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d321895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d321896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d321897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106325 (p : Pattern) (ha : d46864 p = 1) (hb : d321903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d321898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106324 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d321899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d321900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d321901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d321902 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321903 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106326 (p : Pattern) (ha : d46864 p = 1) (hb : d367603 p = 1) : d356088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44916 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105938 q ha hb
    | true =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h2 (q : Pattern) (ha : d44976 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44976, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44977 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44977, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44978 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44979 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367603 q = 1) : d356088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367603, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367603, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro106327 (p : Pattern) (ha : d46864 p = 1) (hb : d367613 p = 1) : d356134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44952 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105943 q ha hb
    | true =>
      simp only [d44952, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367609 q = 1) : d356130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367609, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367609, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367610 q = 1) : d356131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367610, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367610, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367611 q = 1) : d356132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367611, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367611, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367612 q = 1) : d356133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367612, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367612, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367613 q = 1) : d356134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367613, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367613, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106328 (p : Pattern) (ha : d46864 p = 1) (hb : d367619 p = 1) : d356957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44981 q = 1) (hb : d46864 q = 1) : d355869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105946 q ha hb
    | true =>
      simp only [d44981, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105947 q ha hb
  have h2 (q : Pattern) (ha : d44982 q = 1) (hb : d46864 q = 1) : d355870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44982, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367601 q = 1) : d356947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367601, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367601, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367602 q = 1) : d356948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367602, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367602, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367604 q = 1) : d356089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367604, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367604, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106326 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367605 q = 1) : d356949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367605, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367605, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d367606 q = 1) : d356950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367606, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367606, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d367607 q = 1) : d356951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367607, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367607, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d367608 q = 1) : d356952 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367608, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367608, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d367614 q = 1) : d356135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367614, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367614, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106327 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d367615 q = 1) : d356953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367615, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367615, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d367616 q = 1) : d356954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367616, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367616, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d367617 q = 1) : d356955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367617, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367617, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d367618 q = 1) : d356956 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367618, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367618, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d367619 q = 1) : d356957 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367619, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367619, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106329 (p : Pattern) (ha : d46864 p = 1) (hb : d367625 p = 1) : d356963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96940 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367620 q = 1) : d356958 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367620, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367620, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106328 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d367621 q = 1) : d356959 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367621, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367621, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d367622 q = 1) : d356960 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367622, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367622, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d367623 q = 1) : d356961 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367623, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367623, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d367624 q = 1) : d356962 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367624, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367624, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d367625 q = 1) : d356963 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367625, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367625, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106330 (p : Pattern) (ha : d46864 p = 1) (hb : d367628 p = 1) : d375171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45200 q = 1) (hb : d46864 q = 1) : d374380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105977 q ha hb
    | true =>
      simp only [d45200, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105978 q ha hb
  have h2 (q : Pattern) (ha : d45201 q = 1) (hb : d46864 q = 1) : d374441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45201, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45202 q = 1) (hb : d46864 q = 1) : d374442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45202, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45203 q = 1) (hb : d46864 q = 1) : d374443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45204 q = 1) (hb : d46864 q = 1) : d374444 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367628 q = 1) : d375171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367628, d375171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367628, d375171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro106331 (p : Pattern) (ha : d46864 p = 1) (hb : d367639 p = 1) : d375181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367634 q = 1) : d374416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367634, d374416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106014 q hb ha
    | true =>
      simp only [d367634, d374416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105984 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367635 q = 1) : d375177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367635, d375177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367635, d375177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367636 q = 1) : d375178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367636, d375178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367636, d375178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367637 q = 1) : d375179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367637, d375179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367637, d375179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367638 q = 1) : d375180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367638, d375180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367638, d375180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367639 q = 1) : d375181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367639, d375181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367639, d375181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106332 (p : Pattern) (ha : d46864 p = 1) (hb : d367645 p = 1) : d375187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45206 q = 1) (hb : d46864 q = 1) : d374446 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45206, d374446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105976 q ha hb
    | true =>
      simp only [d45206, d374446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105979 q ha hb
  have h2 (q : Pattern) (ha : d45207 q = 1) (hb : d46864 q = 1) : d374447 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45207, d374447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45207, d374447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367626 q = 1) : d375169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367626, d375169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367626, d375169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367627 q = 1) : d375170 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367627, d375170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367627, d375170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367629 q = 1) : d375172 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367629, d375172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367629, d375172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106330 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367630 q = 1) : d375173 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367630, d375173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367630, d375173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d367631 q = 1) : d375174 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367631, d375174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367631, d375174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d367632 q = 1) : d375175 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367632, d375175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367632, d375175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d367633 q = 1) : d375176 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367633, d375176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367633, d375176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d367640 q = 1) : d375182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367640, d375182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367640, d375182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106331 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d367641 q = 1) : d375183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367641, d375183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367641, d375183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d367642 q = 1) : d375184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367642, d375184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367642, d375184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d367643 q = 1) : d375185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367643, d375185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367643, d375185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d367644 q = 1) : d375186 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367644, d375186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367644, d375186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d367645 q = 1) : d375187 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367645, d375187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367645, d375187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106333 (p : Pattern) (ha : d46864 p = 1) (hb : d367651 p = 1) : d375193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367646 q = 1) : d375188 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367646, d375188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367646, d375188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106332 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367647 q = 1) : d375189 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367647, d375189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367647, d375189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367648 q = 1) : d375190 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367648, d375190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367648, d375190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367649 q = 1) : d375191 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367649, d375191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367649, d375191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367650 q = 1) : d375192 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367650, d375192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367650, d375192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367651 q = 1) : d375193 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367651, d375193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367651, d375193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106334 (p : Pattern) (ha : d46864 p = 1) (hb : d367655 p = 1) : d375197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45542 q = 1) (hb : d46864 q = 1) : d374614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, d374614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106028 q ha hb
    | true =>
      simp only [d45542, d374614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106029 q ha hb
  have h2 (q : Pattern) (ha : d45543 q = 1) (hb : d46864 q = 1) : d374615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d374615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45543, d374615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45544 q = 1) (hb : d46864 q = 1) : d374616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d374616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45544, d374616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45545 q = 1) (hb : d46864 q = 1) : d374617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d374617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45545, d374617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45546 q = 1) (hb : d46864 q = 1) : d374618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d374618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45546, d374618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367655 q = 1) : d375197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367655, d375197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367655, d375197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro106335 (p : Pattern) (ha : d46864 p = 1) (hb : d367666 p = 1) : d375208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367661 q = 1) : d375203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367661, d375203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106069 q hb ha
    | true =>
      simp only [d367661, d375203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106037 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367662 q = 1) : d375204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367662, d375204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367662, d375204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367663 q = 1) : d375205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367663, d375205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367663, d375205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367664 q = 1) : d375206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367664, d375206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367664, d375206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367665 q = 1) : d375207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367665, d375207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367665, d375207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367666 q = 1) : d375208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367666, d375208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367666, d375208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106336 (p : Pattern) (ha : d46864 p = 1) (hb : d367672 p = 1) : d375214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45548 q = 1) (hb : d46864 q = 1) : d374620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, d374620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106027 q ha hb
    | true =>
      simp only [d45548, d374620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106030 q ha hb
  have h2 (q : Pattern) (ha : d45549 q = 1) (hb : d46864 q = 1) : d374621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, d374621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45549, d374621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367653 q = 1) : d375195 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367653, d375195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367653, d375195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367654 q = 1) : d375196 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367654, d375196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367654, d375196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367656 q = 1) : d375198 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367656, d375198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367656, d375198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106334 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367657 q = 1) : d375199 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367657, d375199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367657, d375199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d367658 q = 1) : d375200 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367658, d375200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367658, d375200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d367659 q = 1) : d375201 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367659, d375201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367659, d375201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d367660 q = 1) : d375202 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367660, d375202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367660, d375202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d367667 q = 1) : d375209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367667, d375209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367667, d375209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106335 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d367668 q = 1) : d375210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367668, d375210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367668, d375210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d367669 q = 1) : d375211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367669, d375211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367669, d375211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d367670 q = 1) : d375212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367670, d375212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367670, d375212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d367671 q = 1) : d375213 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367671, d375213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367671, d375213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d367672 q = 1) : d375214 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367672, d375214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367672, d375214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106337 (p : Pattern) (ha : d46864 p = 1) (hb : d367678 p = 1) : d375220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367673 q = 1) : d375215 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367673, d375215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367673, d375215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106336 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367674 q = 1) : d375216 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367674, d375216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367674, d375216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367675 q = 1) : d375217 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367675, d375217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367675, d375217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367676 q = 1) : d375218 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367676, d375218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367676, d375218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367677 q = 1) : d375219 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367677, d375219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367677, d375219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367678 q = 1) : d375220 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367678, d375220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367678, d375220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106338 (p : Pattern) (ha : d46864 p = 1) (hb : d367683 p = 1) : d375225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46006 q = 1) (hb : d46864 q = 1) : d374868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106090 q ha hb
    | true =>
      simp only [d46006, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106091 q ha hb
  have h2 (q : Pattern) (ha : d46007 q = 1) (hb : d46864 q = 1) : d374869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46007, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46008 q = 1) (hb : d46864 q = 1) : d374870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46008, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46009 q = 1) (hb : d46864 q = 1) : d374871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46009, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46010 q = 1) (hb : d46864 q = 1) : d374872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46010, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367683 q = 1) : d375225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367683, d375225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367683, d375225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro106339 (p : Pattern) (ha : d46864 p = 1) (hb : d367694 p = 1) : d375236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367689 q = 1) : d375231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367689, d375231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106132 q hb ha
    | true =>
      simp only [d367689, d375231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106099 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367690 q = 1) : d375232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367690, d375232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367690, d375232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367691 q = 1) : d375233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367691, d375233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367691, d375233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367692 q = 1) : d375234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367692, d375234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367692, d375234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367693 q = 1) : d375235 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367693, d375235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367693, d375235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367694 q = 1) : d375236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367694, d375236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367694, d375236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106340 (p : Pattern) (ha : d46864 p = 1) (hb : d367700 p = 1) : d375242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46012 q = 1) (hb : d46864 q = 1) : d374874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d374874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106089 q ha hb
    | true =>
      simp only [d46012, d374874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106092 q ha hb
  have h2 (q : Pattern) (ha : d46013 q = 1) (hb : d46864 q = 1) : d374875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d374875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46013, d374875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367681 q = 1) : d375223 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367681, d375223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d367681, d375223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367682 q = 1) : d375224 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367682, d375224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367682, d375224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367684 q = 1) : d375226 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367684, d375226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367684, d375226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106338 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367685 q = 1) : d375227 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367685, d375227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367685, d375227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d367686 q = 1) : d375228 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367686, d375228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367686, d375228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d367687 q = 1) : d375229 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367687, d375229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367687, d375229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d367688 q = 1) : d375230 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367688, d375230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367688, d375230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d367695 q = 1) : d375237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367695, d375237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367695, d375237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106339 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d367696 q = 1) : d375238 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367696, d375238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367696, d375238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d367697 q = 1) : d375239 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367697, d375239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367697, d375239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d367698 q = 1) : d375240 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367698, d375240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367698, d375240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d367699 q = 1) : d375241 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367699, d375241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367699, d375241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d367700 q = 1) : d375242 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367700, d375242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367700, d375242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106341 (p : Pattern) (ha : d46864 p = 1) (hb : d367706 p = 1) : d375248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367701 q = 1) : d375243 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367701, d375243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367701, d375243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106340 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367702 q = 1) : d375244 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367702, d375244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367702, d375244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367703 q = 1) : d375245 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367703, d375245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367703, d375245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367704 q = 1) : d375246 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367704, d375246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367704, d375246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367705 q = 1) : d375247 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367705, d375247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367705, d375247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367706 q = 1) : d375248 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367706, d375248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367706, d375248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106342 (p : Pattern) (ha : d46864 p = 1) (hb : d367712 p = 1) : d375254 p = 1 := by
  have h0 (q : Pattern) (ha : d46864 q = 1) (hb : d367652 q = 1) : d375194 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367652, d375194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106329 q ha hb
    | true =>
      simp only [d367652, d375194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106333 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367679 q = 1) : d375221 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367679, d375221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367679, d375221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106337 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367680 q = 1) : d375222 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367680, d375222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d367680, d375222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367707 q = 1) : d375249 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367707, d375249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367707, d375249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106341 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367708 q = 1) : d375250 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367708, d375250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367708, d375250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367709 q = 1) : d375251 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d367709, d375251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367709, d375251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106325 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d367710 q = 1) : d375252 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d367710, d375252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367710, d375252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d326621 q = 1) : d326621 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d367711 q = 1) : d375253 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d367711, d375253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367711, d375253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d367712 q = 1) : d375254 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d367712, d375254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367712, d375254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro106343 (p : Pattern) (ha : d46864 p = 1) (hb : d367718 p = 1) : d375260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367713 q = 1) : d375255 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d367713, d375255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106342 q ha hb
    | true =>
      simp only [d367713, d375255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367714 q = 1) : d375256 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d367714, d375256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367714, d375256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367715 q = 1) : d375257 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d367715, d375257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367715, d375257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367716 q = 1) : d375258 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d367716, d375258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367716, d375258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367717 q = 1) : d375259 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d367717, d375259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367717, d375259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367718 q = 1) : d375260 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d367718, d375260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367718, d375260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106344 (p : Pattern) (ha : d46864 p = 1) (hb : d367724 p = 1) : d375266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367719 q = 1) : d375261 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d367719, d375261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106343 q ha hb
    | true =>
      simp only [d367719, d375261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367720 q = 1) : d375262 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d367720, d375262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367720, d375262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367721 q = 1) : d375263 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d367721, d375263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367721, d375263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367722 q = 1) : d375264 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d375264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367722, d375264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367723 q = 1) : d375265 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d375265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367723, d375265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367724 q = 1) : d375266 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, d375266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367724, d375266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106345 (p : Pattern) (ha : d46864 p = 1) (hb : d367730 p = 1) : d375272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367725 q = 1) : d375267 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, d375267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106344 q ha hb
    | true =>
      simp only [d367725, d375267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367726 q = 1) : d375268 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, d375268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, d375268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367727 q = 1) : d375269 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, d375269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, d375269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367728 q = 1) : d375270 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, d375270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, d375270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367729 q = 1) : d375271 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, d375271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, d375271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367730 q = 1) : d375272 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, d375272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, d375272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106346 (p : Pattern) (ha : d46864 p = 1) (hb : d367736 p = 1) : d375278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367731 q = 1) : d375273 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, d375273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106345 q ha hb
    | true =>
      simp only [d367731, d375273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367732 q = 1) : d375274 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, d375274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, d375274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367733 q = 1) : d375275 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, d375275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, d375275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367734 q = 1) : d375276 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, d375276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, d375276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367735 q = 1) : d375277 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, d375277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, d375277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367736 q = 1) : d375278 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, d375278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, d375278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106347 (p : Pattern) (ha : d46864 p = 1) (hb : d367742 p = 1) : d375284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367737 q = 1) : d375279 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, d375279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106346 q ha hb
    | true =>
      simp only [d367737, d375279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367738 q = 1) : d375280 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, d375280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, d375280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367739 q = 1) : d375281 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, d375281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, d375281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367740 q = 1) : d375282 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, d375282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, d375282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367741 q = 1) : d375283 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, d375283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, d375283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367742 q = 1) : d375284 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, d375284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, d375284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106348 (p : Pattern) (ha : d46864 p = 1) (hb : d367748 p = 1) : d375290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367743 q = 1) : d375285 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, d375285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106347 q ha hb
    | true =>
      simp only [d367743, d375285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367744 q = 1) : d375286 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, d375286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, d375286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367745 q = 1) : d375287 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, d375287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, d375287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367746 q = 1) : d375288 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, d375288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, d375288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367747 q = 1) : d375289 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, d375289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, d375289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367748 q = 1) : d375290 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, d375290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, d375290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106349 (p : Pattern) (ha : d46864 p = 1) (hb : d367754 p = 1) : d375296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d367749 q = 1) : d375291 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, d375291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106348 q ha hb
    | true =>
      simp only [d367749, d375291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d367750 q = 1) : d375292 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, d375292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, d375292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d367751 q = 1) : d375293 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, d375293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, d375293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d367752 q = 1) : d375294 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, d375294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, d375294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d367753 q = 1) : d375295 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, d375295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, d375295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d367754 q = 1) : d375296 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, d375296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, d375296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106350 (p : Pattern) (ha : d341234 p = 1) (hb : d355861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341195 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d341229 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341117 q = 1) (hb : d355799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341117, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106151 q ha hb
    | true =>
      simp only [d341117, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d341230 q = 1) (hb : d355857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341230, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d341230, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341118 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d341231 q = 1) (hb : d355858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341231, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341231, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d341232 q = 1) (hb : d355859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341232, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341232, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341233 q = 1) (hb : d355860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341233, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341233, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d341234 q = 1) (hb : d355861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341234, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341234, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106351 (p : Pattern) (ha : d341250 p = 1) (hb : d355868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341195 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341201 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341229 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341117 q = 1) (hb : d355799 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341117, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106151 q ha hb
    | true =>
      simp only [d341117, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d341230 q = 1) (hb : d355857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341230, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d341230, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341118 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d341231 q = 1) (hb : d355858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341231, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d341231, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d341232 q = 1) (hb : d355859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341232, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341232, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d341233 q = 1) (hb : d355860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341233, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341233, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d341239 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d341243 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d341245 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d341124 q = 1) (hb : d355806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341124, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106153 q ha hb
    | true =>
      simp only [d341124, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d341246 q = 1) (hb : d355864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341246, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d341246, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d341125 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d341247 q = 1) (hb : d355865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341247, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341247, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d341248 q = 1) (hb : d355866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341248, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d341248, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d341249 q = 1) (hb : d355867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341249, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d341249, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d341250 q = 1) (hb : d355868 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341250, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341250, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106352 (p : Pattern) (ha : d341259 p = 1) (hb : d356088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341245 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341124 q = 1) (hb : d355806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341124, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106153 q ha hb
    | true =>
      simp only [d341124, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341246 q = 1) (hb : d355864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341246, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341246, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341125 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341247 q = 1) (hb : d355865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341247, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341247, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341257 q = 1) (hb : d355866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341257, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341257, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341258 q = 1) (hb : d355867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341258, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341258, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341259 q = 1) (hb : d356088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341259, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341259, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106353 (p : Pattern) (ha : d341288 p = 1) (hb : d356134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341283 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341158 q = 1) (hb : d355840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341158, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106158 q ha hb
    | true =>
      simp only [d341158, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d341284 q = 1) (hb : d356130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d341284, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341284, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341159 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341285 q = 1) (hb : d356131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d341285, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341285, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341286 q = 1) (hb : d356132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d341286, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341286, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341287 q = 1) (hb : d356133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d341287, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341287, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d341288 q = 1) (hb : d356134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d341288, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341288, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106354 (p : Pattern) (ha : d341294 p = 1) (hb : d356957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d341251 q = 1) (hb : d355869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341251, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106350 q ha hb
    | true =>
      simp only [d341251, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106351 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341254 q = 1) (hb : d355870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341254, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d341254, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d341255 q = 1) (hb : d356947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341255, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d341255, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d341256 q = 1) (hb : d356948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341256, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341256, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341260 q = 1) (hb : d356089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341260, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341260, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106352 q ha hb
  have h8 (q : Pattern) (ha : d341261 q = 1) (hb : d356949 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341261, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d341261, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d341262 q = 1) (hb : d356950 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341262, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d341262, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d341263 q = 1) (hb : d356951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341263, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d341263, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d341264 q = 1) (hb : d356952 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341264, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d341264, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d341289 q = 1) (hb : d356135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d341289, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d341289, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106353 q ha hb
  have h13 (q : Pattern) (ha : d341290 q = 1) (hb : d356953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d341290, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d341290, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d341291 q = 1) (hb : d356954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d341291, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d341291, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d341292 q = 1) (hb : d356955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d341292, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d341292, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d341293 q = 1) (hb : d356956 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d341293, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d341293, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d341294 q = 1) (hb : d356957 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d341294, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d341294, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro106355 (p : Pattern) (ha : d341300 p = 1) (hb : d356963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341174 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341295 q = 1) (hb : d356958 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d341295, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341295, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106354 q ha hb
  have h3 (q : Pattern) (ha : d341296 q = 1) (hb : d356959 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d341296, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341296, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d341297 q = 1) (hb : d356960 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d341297, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341297, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d341298 q = 1) (hb : d356961 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d341298, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341298, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d341299 q = 1) (hb : d356962 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d341299, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d341299, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d341300 q = 1) (hb : d356963 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d341300, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d341300, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro106356 (p : Pattern) (ha : d373096 p = 1) (hb : d374438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341327 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d373091 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d341229 q = 1) (hb : d374373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341229, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106169 q ha hb
    | true =>
      simp only [d341229, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106151 q ha hb
  have h5 (q : Pattern) (ha : d373092 q = 1) (hb : d374434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373092, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d373092, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d341374 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d373093 q = 1) (hb : d374435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373093, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373093, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d373094 q = 1) (hb : d374436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373094, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d373094, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373095 q = 1) (hb : d374437 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373095, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373095, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373096 q = 1) (hb : d374438 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373096, d374438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373096, d374438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106357 (p : Pattern) (ha : d373103 p = 1) (hb : d374445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d341327 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d341229 q = 1) (hb : d374373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341229, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106169 q ha hb
    | true =>
      simp only [d341229, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106151 q ha hb
  have h4 (q : Pattern) (ha : d373092 q = 1) (hb : d374434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373092, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d373092, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d341374 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d373093 q = 1) (hb : d374435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373093, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373093, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d373094 q = 1) (hb : d374436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373094, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373094, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373095 q = 1) (hb : d374437 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373095, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373095, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d341383 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d341387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d373098 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d341245 q = 1) (hb : d374380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341245, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106173 q ha hb
    | true =>
      simp only [d341245, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106153 q ha hb
  have h13 (q : Pattern) (ha : d373099 q = 1) (hb : d374441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373099, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d373099, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d373100 q = 1) (hb : d374442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373100, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373100, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d373101 q = 1) (hb : d374443 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373101, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d373101, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d373102 q = 1) (hb : d374444 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373102, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d373102, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d373103 q = 1) (hb : d374445 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373103, d374445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373103, d374445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106358 (p : Pattern) (ha : d373110 p = 1) (hb : d375171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341245 q = 1) (hb : d374380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341245, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106173 q ha hb
    | true =>
      simp only [d341245, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106153 q ha hb
  have h3 (q : Pattern) (ha : d373099 q = 1) (hb : d374441 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373099, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373099, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373100 q = 1) (hb : d374442 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373100, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373100, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373108 q = 1) (hb : d374443 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373108, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373108, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373109 q = 1) (hb : d374444 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373109, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373109, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373110 q = 1) (hb : d375171 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373110, d375171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373110, d375171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106359 (p : Pattern) (ha : d373139 p = 1) (hb : d375181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373134 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d341283 q = 1) (hb : d374416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d341283, d374416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106179 q ha hb
    | true =>
      simp only [d341283, d374416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106158 q ha hb
  have h3 (q : Pattern) (ha : d373135 q = 1) (hb : d375177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373135, d375177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373135, d375177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d341444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373136 q = 1) (hb : d375178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373136, d375178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373136, d375178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373137 q = 1) (hb : d375179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373137, d375179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373137, d375179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373138 q = 1) (hb : d375180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373138, d375180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373138, d375180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373139 q = 1) (hb : d375181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373139, d375181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373139, d375181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106360 (p : Pattern) (ha : d373145 p = 1) (hb : d375187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d341315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373104 q = 1) (hb : d374446 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373104, d374446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106356 q ha hb
    | true =>
      simp only [d373104, d374446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106357 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d341400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373105 q = 1) (hb : d374447 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373105, d374447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373105, d374447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373106 q = 1) (hb : d375169 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373106, d375169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373106, d375169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373107 q = 1) (hb : d375170 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373107, d375170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373107, d375170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373111 q = 1) (hb : d375172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373111, d375172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d373111, d375172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106358 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d341409 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d373112 q = 1) (hb : d375173 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373112, d375173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373112, d375173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d373113 q = 1) (hb : d375174 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373113, d375174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373113, d375174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d373114 q = 1) (hb : d375175 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373114, d375175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373114, d375175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d373115 q = 1) (hb : d375176 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373115, d375176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373115, d375176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373140 q = 1) (hb : d375182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373140, d375182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d373140, d375182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106359 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d373141 q = 1) (hb : d375183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373141, d375183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373141, d375183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d373142 q = 1) (hb : d375184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373142, d375184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373142, d375184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d373143 q = 1) (hb : d375185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373143, d375185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373143, d375185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d373144 q = 1) (hb : d375186 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373144, d375186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373144, d375186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d373145 q = 1) (hb : d375187 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d373145, d375187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d373145, d375187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106361 (p : Pattern) (ha : d373151 p = 1) (hb : d375193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373146 q = 1) (hb : d375188 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d373146, d375188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373146, d375188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106360 q ha hb
  have h2 (q : Pattern) (ha : d373147 q = 1) (hb : d375189 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d373147, d375189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373147, d375189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373148 q = 1) (hb : d375190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d373148, d375190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373148, d375190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373149 q = 1) (hb : d375191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d373149, d375191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373149, d375191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373150 q = 1) (hb : d375192 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d373150, d375192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373150, d375192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373151 q = 1) (hb : d375193 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d373151, d375193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373151, d375193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106362 (p : Pattern) (ha : d373252 p = 1) (hb : d374609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373190 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d373241 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d373161 q = 1) (hb : d374604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373161, d374604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106220 q ha hb
    | true =>
      simp only [d373161, d374604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106212 q ha hb
  have h5 (q : Pattern) (ha : d373242 q = 1) (hb : d374605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373242, d374605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d373242, d374605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d373248 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d373249 q = 1) (hb : d374606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373249, d374606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373249, d374606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d373250 q = 1) (hb : d374607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373250, d374607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d373250, d374607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373251 q = 1) (hb : d374608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373251, d374608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373251, d374608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373252 q = 1) (hb : d374609 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373252, d374609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373252, d374609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106363 (p : Pattern) (ha : d373271 p = 1) (hb : d374619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373184 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373241 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373161 q = 1) (hb : d374604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373161, d374604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106220 q ha hb
    | true =>
      simp only [d373161, d374604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106212 q ha hb
  have h4 (q : Pattern) (ha : d373242 q = 1) (hb : d374605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373242, d374605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d373242, d374605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d373248 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d373249 q = 1) (hb : d374606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373249, d374606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373249, d374606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d373250 q = 1) (hb : d374607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373250, d374607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373250, d374607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373251 q = 1) (hb : d374608 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373251, d374608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373251, d374608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d373257 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d373261 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d373263 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d373170 q = 1) (hb : d374614 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373170, d374614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106222 q ha hb
    | true =>
      simp only [d373170, d374614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106213 q ha hb
  have h13 (q : Pattern) (ha : d373264 q = 1) (hb : d374615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373264, d374615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d373264, d374615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d373267 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d373268 q = 1) (hb : d374616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373268, d374616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373268, d374616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d373269 q = 1) (hb : d374617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373269, d374617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d373269, d374617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d373270 q = 1) (hb : d374618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373270, d374618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d373270, d374618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d373271 q = 1) (hb : d374619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373271, d374619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373271, d374619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106364 (p : Pattern) (ha : d373280 p = 1) (hb : d375197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373170 q = 1) (hb : d374614 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373170, d374614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106222 q ha hb
    | true =>
      simp only [d373170, d374614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106213 q ha hb
  have h3 (q : Pattern) (ha : d373264 q = 1) (hb : d374615 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373264, d374615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373264, d374615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d373267 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373268 q = 1) (hb : d374616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373268, d374616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373268, d374616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373278 q = 1) (hb : d374617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373278, d374617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373278, d374617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373279 q = 1) (hb : d374618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373279, d374618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373279, d374618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373280 q = 1) (hb : d375197 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373280, d375197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373280, d375197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106365 (p : Pattern) (ha : d373336 p = 1) (hb : d375208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373325 q = 1) (hb : d375203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373325, d375203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106252 q ha hb
    | true =>
      simp only [d373325, d375203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106217 q ha hb
  have h3 (q : Pattern) (ha : d373326 q = 1) (hb : d375204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373326, d375204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373326, d375204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d373332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373333 q = 1) (hb : d375205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373333, d375205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373333, d375205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373334 q = 1) (hb : d375206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373334, d375206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373334, d375206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373335 q = 1) (hb : d375207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373335, d375207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373335, d375207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373336 q = 1) (hb : d375208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373336, d375208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373336, d375208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106366 (p : Pattern) (ha : d373342 p = 1) (hb : d375214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373178 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373272 q = 1) (hb : d374620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373272, d374620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106362 q ha hb
    | true =>
      simp only [d373272, d374620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106363 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373275 q = 1) (hb : d374621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373275, d374621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373275, d374621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373276 q = 1) (hb : d375195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373276, d375195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373276, d375195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373277 q = 1) (hb : d375196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373277, d375196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373277, d375196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373281 q = 1) (hb : d375198 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373281, d375198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d373281, d375198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106364 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d341632 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d373282 q = 1) (hb : d375199 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373282, d375199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373282, d375199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d373283 q = 1) (hb : d375200 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373283, d375200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373283, d375200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d373284 q = 1) (hb : d375201 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373284, d375201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373284, d375201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d373285 q = 1) (hb : d375202 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373285, d375202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373285, d375202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373337 q = 1) (hb : d375209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373337, d375209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d373337, d375209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106365 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d341705 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d373338 q = 1) (hb : d375210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373338, d375210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373338, d375210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d373339 q = 1) (hb : d375211 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373339, d375211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373339, d375211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d373340 q = 1) (hb : d375212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373340, d375212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373340, d375212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d373341 q = 1) (hb : d375213 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373341, d375213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373341, d375213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d373342 q = 1) (hb : d375214 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d373342, d375214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d373342, d375214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106367 (p : Pattern) (ha : d373348 p = 1) (hb : d375220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373343 q = 1) (hb : d375215 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d373343, d375215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373343, d375215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106366 q ha hb
  have h2 (q : Pattern) (ha : d373344 q = 1) (hb : d375216 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d373344, d375216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373344, d375216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373345 q = 1) (hb : d375217 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d373345, d375217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373345, d375217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373346 q = 1) (hb : d375218 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d373346, d375218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373346, d375218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373347 q = 1) (hb : d375219 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d373347, d375219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373347, d375219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373348 q = 1) (hb : d375220 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d373348, d375220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373348, d375220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106368 (p : Pattern) (ha : d373539 p = 1) (hb : d374863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373466 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d373528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d373431 q = 1) (hb : d374858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106267 q ha hb
    | true =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106268 q ha hb
  have h5 (q : Pattern) (ha : d373529 q = 1) (hb : d374859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373529, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d373529, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d373535 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d373536 q = 1) (hb : d374860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373536, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d373536, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d373537 q = 1) (hb : d374861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373537, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d373537, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d373538 q = 1) (hb : d374862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373538, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373538, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d373539 q = 1) (hb : d374863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373539, d374863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373539, d374863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106369 (p : Pattern) (ha : d373560 p = 1) (hb : d374873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373457 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373466 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373431 q = 1) (hb : d374858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106267 q ha hb
    | true =>
      simp only [d373431, d374858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106268 q ha hb
  have h4 (q : Pattern) (ha : d373529 q = 1) (hb : d374859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373529, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d373529, d374859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d373535 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d373536 q = 1) (hb : d374860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373536, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d373536, d374860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d373537 q = 1) (hb : d374861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373537, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373537, d374861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373538 q = 1) (hb : d374862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373538, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373538, d374862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d373545 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d373550 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d373552 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d373441 q = 1) (hb : d374868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373441, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106270 q ha hb
    | true =>
      simp only [d373441, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106271 q ha hb
  have h13 (q : Pattern) (ha : d373553 q = 1) (hb : d374869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373553, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d373553, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d373556 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d373557 q = 1) (hb : d374870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373557, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373557, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d373558 q = 1) (hb : d374871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373558, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d373558, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d373559 q = 1) (hb : d374872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373559, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d373559, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d373560 q = 1) (hb : d374873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373560, d374873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d373560, d374873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106370 (p : Pattern) (ha : d373580 p = 1) (hb : d375225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373441 q = 1) (hb : d374868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373441, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106270 q ha hb
    | true =>
      simp only [d373441, d374868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106271 q ha hb
  have h3 (q : Pattern) (ha : d373553 q = 1) (hb : d374869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373553, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373553, d374869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d373556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373557 q = 1) (hb : d374870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373557, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373557, d374870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373578 q = 1) (hb : d374871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373578, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373578, d374871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373579 q = 1) (hb : d374872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373579, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373579, d374872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373580 q = 1) (hb : d375225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373580, d375225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373580, d375225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106371 (p : Pattern) (ha : d373687 p = 1) (hb : d375236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d373671 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373676 q = 1) (hb : d375231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d373676, d375231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106307 q ha hb
    | true =>
      simp only [d373676, d375231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106310 q ha hb
  have h3 (q : Pattern) (ha : d373677 q = 1) (hb : d375232 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d373677, d375232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373677, d375232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d373683 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373684 q = 1) (hb : d375233 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d373684, d375233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373684, d375233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373685 q = 1) (hb : d375234 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373685, d375234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373685, d375234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373686 q = 1) (hb : d375235 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d373686, d375235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373686, d375235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d373687 q = 1) (hb : d375236 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d373687, d375236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373687, d375236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106372 (p : Pattern) (ha : d373700 p = 1) (hb : d375242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d373449 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373561 q = 1) (hb : d374874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373561, d374874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106368 q ha hb
    | true =>
      simp only [d373561, d374874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106369 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d373574 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d373575 q = 1) (hb : d374875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373575, d374875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d373575, d374875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d373576 q = 1) (hb : d375223 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373576, d375223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373576, d375223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d373577 q = 1) (hb : d375224 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373577, d375224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373577, d375224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d373581 q = 1) (hb : d375226 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373581, d375226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d373581, d375226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106370 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d373583 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d373584 q = 1) (hb : d375227 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373584, d375227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d373584, d375227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d373585 q = 1) (hb : d375228 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373585, d375228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d373585, d375228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d373586 q = 1) (hb : d375229 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373586, d375229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d373586, d375229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d373587 q = 1) (hb : d375230 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373587, d375230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d373587, d375230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d373688 q = 1) (hb : d375237 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d373688, d375237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d373688, d375237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106371 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d373695 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d373696 q = 1) (hb : d375238 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d373696, d375238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d373696, d375238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d373697 q = 1) (hb : d375239 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d373697, d375239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d373697, d375239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d373698 q = 1) (hb : d375240 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d373698, d375240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d373698, d375240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d373699 q = 1) (hb : d375241 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d373699, d375241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d373699, d375241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d373700 q = 1) (hb : d375242 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d373700, d375242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d373700, d375242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106373 (p : Pattern) (ha : d373706 p = 1) (hb : d375248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d373701 q = 1) (hb : d375243 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d373701, d375243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373701, d375243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106372 q ha hb
  have h2 (q : Pattern) (ha : d373702 q = 1) (hb : d375244 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d373702, d375244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373702, d375244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d373703 q = 1) (hb : d375245 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d373703, d375245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373703, d375245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373704 q = 1) (hb : d375246 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d373704, d375246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373704, d375246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d373705 q = 1) (hb : d375247 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d373705, d375247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373705, d375247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373706 q = 1) (hb : d375248 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d373706, d375248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d373706, d375248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106374 (p : Pattern) (ha : d374306 p = 1) (hb : d375254 p = 1) : d375298 p = 1 := by
  have h0 (q : Pattern) (ha : d373152 q = 1) (hb : d375194 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d373152, d375194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106355 q ha hb
    | true =>
      simp only [d373152, d375194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106361 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d373349 q = 1) (hb : d375221 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d373349, d375221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373349, d375221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106367 q ha hb
  have h3 (q : Pattern) (ha : d373350 q = 1) (hb : d375222 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d373350, d375222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d373350, d375222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d373707 q = 1) (hb : d375249 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d373707, d375249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373707, d375249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106373 q ha hb
  have h5 (q : Pattern) (ha : d373708 q = 1) (hb : d375250 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d373708, d375250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d373708, d375250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d373709 q = 1) (hb : d375251 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d373709, d375251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d373709, d375251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d374062 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d374063 q = 1) (hb : d375252 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d374063, d375252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d374063, d375252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d326621 q = 1) (hb : d374304 q = 1) : d326621 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d374305 q = 1) (hb : d375253 q = 1) : d375297 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d374305, d375253, d375297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d374305, d375253, d375297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d374306 q = 1) (hb : d375254 q = 1) : d375298 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d374306, d375254, d375298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d374306, d375254, d375298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h11 p ha hb
theorem andIntro106375 (p : Pattern) (ha : d374312 p = 1) (hb : d375260 p = 1) : d375304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374307 q = 1) (hb : d375255 q = 1) : d375299 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d374307, d375255, d375299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106374 q ha hb
    | true =>
      simp only [d374307, d375255, d375299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374308 q = 1) (hb : d375256 q = 1) : d375300 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d374308, d375256, d375300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374308, d375256, d375300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374309 q = 1) (hb : d375257 q = 1) : d375301 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d374309, d375257, d375301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374309, d375257, d375301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374310 q = 1) (hb : d375258 q = 1) : d375302 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d374310, d375258, d375302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374310, d375258, d375302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374311 q = 1) (hb : d375259 q = 1) : d375303 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d374311, d375259, d375303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374311, d375259, d375303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374312 q = 1) (hb : d375260 q = 1) : d375304 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d374312, d375260, d375304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374312, d375260, d375304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106376 (p : Pattern) (ha : d374318 p = 1) (hb : d375266 p = 1) : d375310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374313 q = 1) (hb : d375261 q = 1) : d375305 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d374313, d375261, d375305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106375 q ha hb
    | true =>
      simp only [d374313, d375261, d375305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374314 q = 1) (hb : d375262 q = 1) : d375306 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d374314, d375262, d375306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374314, d375262, d375306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374315 q = 1) (hb : d375263 q = 1) : d375307 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d374315, d375263, d375307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374315, d375263, d375307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374316 q = 1) (hb : d375264 q = 1) : d375308 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d374316, d375264, d375308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374316, d375264, d375308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374317 q = 1) (hb : d375265 q = 1) : d375309 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d374317, d375265, d375309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374317, d375265, d375309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374318 q = 1) (hb : d375266 q = 1) : d375310 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d374318, d375266, d375310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374318, d375266, d375310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106377 (p : Pattern) (ha : d374324 p = 1) (hb : d375272 p = 1) : d375316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374319 q = 1) (hb : d375267 q = 1) : d375311 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d374319, d375267, d375311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106376 q ha hb
    | true =>
      simp only [d374319, d375267, d375311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374320 q = 1) (hb : d375268 q = 1) : d375312 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d374320, d375268, d375312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374320, d375268, d375312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374321 q = 1) (hb : d375269 q = 1) : d375313 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d374321, d375269, d375313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374321, d375269, d375313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374322 q = 1) (hb : d375270 q = 1) : d375314 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d374322, d375270, d375314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374322, d375270, d375314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374323 q = 1) (hb : d375271 q = 1) : d375315 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d374323, d375271, d375315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374323, d375271, d375315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374324 q = 1) (hb : d375272 q = 1) : d375316 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d374324, d375272, d375316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374324, d375272, d375316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106378 (p : Pattern) (ha : d374330 p = 1) (hb : d375278 p = 1) : d375322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374325 q = 1) (hb : d375273 q = 1) : d375317 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d374325, d375273, d375317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106377 q ha hb
    | true =>
      simp only [d374325, d375273, d375317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374326 q = 1) (hb : d375274 q = 1) : d375318 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d374326, d375274, d375318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374326, d375274, d375318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374327 q = 1) (hb : d375275 q = 1) : d375319 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d374327, d375275, d375319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374327, d375275, d375319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374328 q = 1) (hb : d375276 q = 1) : d375320 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d374328, d375276, d375320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374328, d375276, d375320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374329 q = 1) (hb : d375277 q = 1) : d375321 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d374329, d375277, d375321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374329, d375277, d375321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374330 q = 1) (hb : d375278 q = 1) : d375322 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d374330, d375278, d375322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374330, d375278, d375322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106379 (p : Pattern) (ha : d374336 p = 1) (hb : d375284 p = 1) : d375328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374331 q = 1) (hb : d375279 q = 1) : d375323 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d374331, d375279, d375323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106378 q ha hb
    | true =>
      simp only [d374331, d375279, d375323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374332 q = 1) (hb : d375280 q = 1) : d375324 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d374332, d375280, d375324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374332, d375280, d375324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374333 q = 1) (hb : d375281 q = 1) : d375325 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d374333, d375281, d375325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374333, d375281, d375325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374334 q = 1) (hb : d375282 q = 1) : d375326 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d374334, d375282, d375326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374334, d375282, d375326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374335 q = 1) (hb : d375283 q = 1) : d375327 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d374335, d375283, d375327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374335, d375283, d375327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374336 q = 1) (hb : d375284 q = 1) : d375328 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d374336, d375284, d375328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374336, d375284, d375328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106380 (p : Pattern) (ha : d374342 p = 1) (hb : d375290 p = 1) : d375334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374337 q = 1) (hb : d375285 q = 1) : d375329 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d374337, d375285, d375329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106379 q ha hb
    | true =>
      simp only [d374337, d375285, d375329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374338 q = 1) (hb : d375286 q = 1) : d375330 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d374338, d375286, d375330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374338, d375286, d375330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374339 q = 1) (hb : d375287 q = 1) : d375331 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d374339, d375287, d375331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374339, d375287, d375331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374340 q = 1) (hb : d375288 q = 1) : d375332 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d374340, d375288, d375332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374340, d375288, d375332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374341 q = 1) (hb : d375289 q = 1) : d375333 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d374341, d375289, d375333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374341, d375289, d375333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374342 q = 1) (hb : d375290 q = 1) : d375334 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d374342, d375290, d375334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374342, d375290, d375334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106381 (p : Pattern) (ha : d374348 p = 1) (hb : d375296 p = 1) : d375340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374343 q = 1) (hb : d375291 q = 1) : d375335 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d374343, d375291, d375335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106380 q ha hb
    | true =>
      simp only [d374343, d375291, d375335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d374344 q = 1) (hb : d375292 q = 1) : d375336 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d374344, d375292, d375336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374344, d375292, d375336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d374345 q = 1) (hb : d375293 q = 1) : d375337 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d374345, d375293, d375337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374345, d375293, d375337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d374346 q = 1) (hb : d375294 q = 1) : d375338 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d374346, d375294, d375338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374346, d375294, d375338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d374347 q = 1) (hb : d375295 q = 1) : d375339 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d374347, d375295, d375339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374347, d375295, d375339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d374348 q = 1) (hb : d375296 q = 1) : d375340 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d374348, d375296, d375340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374348, d375296, d375340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro106382 (p : Pattern) (ha : d46921 p = 1) (hb : d375511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d372762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d372771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d372785 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46917 q = 1) (hb : d375507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d375507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46917, d375507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d372839 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46918 q = 1) (hb : d375508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d375508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46918, d375508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46919 q = 1) (hb : d375509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d375509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46919, d375509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46920 q = 1) (hb : d375510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d375510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46920, d375510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46921 q = 1) (hb : d375511 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d375511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d375511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106383 (p : Pattern) (ha : d46931 p = 1) (hb : d375516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d372762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d372771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d372785 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46917 q = 1) (hb : d375507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d375507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46917, d375507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d372839 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46918 q = 1) (hb : d375508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d375508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46918, d375508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46919 q = 1) (hb : d375509 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d375509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46919, d375509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46920 q = 1) (hb : d375510 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d375510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d375510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d372849 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d372854 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d372856 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46927 q = 1) (hb : d375512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d375512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46927, d375512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d372863 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46928 q = 1) (hb : d375513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d375513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46928, d375513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46929 q = 1) (hb : d375514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d375514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46929, d375514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46930 q = 1) (hb : d375515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d375515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46930, d375515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46931 q = 1) (hb : d375516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d375516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46931, d375516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106384 (p : Pattern) (ha : d321910 p = 1) (hb : d375523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d372856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46927 q = 1) (hb : d375512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d375512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46927, d375512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d372863 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46928 q = 1) (hb : d375513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d375513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46928, d375513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46929 q = 1) (hb : d375521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d375521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d375521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46930 q = 1) (hb : d375522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d375522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d375522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d321910 q = 1) (hb : d375523 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321910, d375523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321910, d375523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106385 (p : Pattern) (ha : d326605 p = 1) (hb : d375533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d372942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d326601 q = 1) (hb : d375529 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d326601, d375529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d326601, d375529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d372988 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d326602 q = 1) (hb : d375530 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d326602, d375530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d326602, d375530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d326603 q = 1) (hb : d375531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d326603, d375531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326603, d375531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d326604 q = 1) (hb : d375532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d326604, d375532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326604, d375532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d326605 q = 1) (hb : d375533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d326605, d375533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326605, d375533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106386 (p : Pattern) (ha : d326611 p = 1) (hb : d375539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d372754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d375517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d375517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106382 q ha hb
    | true =>
      simp only [d46932, d375517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106383 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d372881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d375518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d375518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d375518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d321908 q = 1) (hb : d375519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321908, d375519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d321908, d375519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d321909 q = 1) (hb : d375520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321909, d375520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321909, d375520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321911 q = 1) (hb : d375524 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321911, d375524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321911, d375524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106384 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d372890 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d321912 q = 1) (hb : d375525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321912, d375525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321912, d375525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d321913 q = 1) (hb : d375526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321913, d375526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321913, d375526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d321914 q = 1) (hb : d375527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321914, d375527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321914, d375527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d321915 q = 1) (hb : d375528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321915, d375528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321915, d375528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d326606 q = 1) (hb : d375534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d326606, d375534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d326606, d375534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106385 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d373004 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d326607 q = 1) (hb : d375535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d326607, d375535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d326607, d375535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d326608 q = 1) (hb : d375536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d326608, d375536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d326608, d375536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d326609 q = 1) (hb : d375537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d326609, d375537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d326609, d375537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d326610 q = 1) (hb : d375538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d326610, d375538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d326610, d375538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d326611 q = 1) (hb : d375539 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d326611, d375539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d326611, d375539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106387 (p : Pattern) (ha : d326617 p = 1) (hb : d375545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d326612 q = 1) (hb : d375540 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d326612, d375540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326612, d375540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106386 q ha hb
  have h2 (q : Pattern) (ha : d326613 q = 1) (hb : d375541 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d326613, d375541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326613, d375541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d326614 q = 1) (hb : d375542 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d326614, d375542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326614, d375542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d326615 q = 1) (hb : d375543 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d326615, d375543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326615, d375543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d326616 q = 1) (hb : d375544 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d326616, d375544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326616, d375544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d326617 q = 1) (hb : d375545 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d326617, d375545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326617, d375545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106388 (p : Pattern) (ha : d344144 p = 1) (hb : d355861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d338988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d338994 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d339022 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d355799 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344140 q = 1) (hb : d355857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344140, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d344140, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d338911 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d344141 q = 1) (hb : d355858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344141, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d344141, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d344142 q = 1) (hb : d355859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344142, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d344142, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d344143 q = 1) (hb : d355860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344143, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d344143, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d344144 q = 1) (hb : d355861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344144, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344144, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106389 (p : Pattern) (ha : d344149 p = 1) (hb : d355868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d338994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339022 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d355799 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d344140 q = 1) (hb : d355857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344140, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d344140, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d338911 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d344141 q = 1) (hb : d355858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344141, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344141, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d344142 q = 1) (hb : d355859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344142, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d344142, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344143 q = 1) (hb : d355860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344143, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d344143, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d339060 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d339064 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d339066 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d355806 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d344145 q = 1) (hb : d355864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344145, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d344145, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d338918 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d344146 q = 1) (hb : d355865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344146, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d344146, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d344147 q = 1) (hb : d355866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344147, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d344147, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d344148 q = 1) (hb : d355867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344148, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d344148, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d344149 q = 1) (hb : d355868 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344149, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d344149, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106390 (p : Pattern) (ha : d344156 p = 1) (hb : d356088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d355806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d344145 q = 1) (hb : d355864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344145, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d344145, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d338918 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344146 q = 1) (hb : d355865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344146, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344146, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d344154 q = 1) (hb : d355866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344154, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344154, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344155 q = 1) (hb : d355867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344155, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344155, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344156 q = 1) (hb : d356088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344156, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344156, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106391 (p : Pattern) (ha : d344166 p = 1) (hb : d356134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d355840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d344162 q = 1) (hb : d356130 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d344162, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d344162, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d338952 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344163 q = 1) (hb : d356131 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d344163, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344163, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d344164 q = 1) (hb : d356132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d344164, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344164, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344165 q = 1) (hb : d356133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d344165, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344165, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d344166 q = 1) (hb : d356134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d344166, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d344166, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106392 (p : Pattern) (ha : d344172 p = 1) (hb : d356957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338982 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d344150 q = 1) (hb : d355869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344150, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106388 q ha hb
    | true =>
      simp only [d344150, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106389 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d344151 q = 1) (hb : d355870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344151, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344151, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d344152 q = 1) (hb : d356947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344152, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d344152, d356947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344153 q = 1) (hb : d356948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344153, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d344153, d356948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344157 q = 1) (hb : d356089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344157, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344157, d356089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106390 q ha hb
  have h8 (q : Pattern) (ha : d344158 q = 1) (hb : d356949 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344158, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d344158, d356949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d344159 q = 1) (hb : d356950 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344159, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d344159, d356950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d344160 q = 1) (hb : d356951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344160, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d344160, d356951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d344161 q = 1) (hb : d356952 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344161, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d344161, d356952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d344167 q = 1) (hb : d356135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d344167, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d344167, d356135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106391 q ha hb
  have h13 (q : Pattern) (ha : d344168 q = 1) (hb : d356953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d344168, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d344168, d356953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d344169 q = 1) (hb : d356954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d344169, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d344169, d356954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d344170 q = 1) (hb : d356955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d344170, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d344170, d356955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d344171 q = 1) (hb : d356956 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d344171, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d344171, d356956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d344172 q = 1) (hb : d356957 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d344172, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d344172, d356957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro106393 (p : Pattern) (ha : d344178 p = 1) (hb : d356963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d338967 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d344173 q = 1) (hb : d356958 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d344173, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344173, d356958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106392 q ha hb
  have h3 (q : Pattern) (ha : d344174 q = 1) (hb : d356959 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d344174, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344174, d356959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d344175 q = 1) (hb : d356960 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d344175, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344175, d356960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d344176 q = 1) (hb : d356961 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d344176, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344176, d356961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d344177 q = 1) (hb : d356962 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d344177, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d344177, d356962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d344178 q = 1) (hb : d356963 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d344178, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d344178, d356963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro106394 (p : Pattern) (ha : d374438 p = 1) (hb : d375345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339169 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d371381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d374373 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d374434 q = 1) (hb : d375341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374434, d375341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374434, d375341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d339244 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d374435 q = 1) (hb : d375342 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374435, d375342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374435, d375342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d374436 q = 1) (hb : d375343 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374436, d375343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374436, d375343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d374437 q = 1) (hb : d375344 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374437, d375344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374437, d375344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d374438 q = 1) (hb : d375345 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d374438, d375345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374438, d375345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106395 (p : Pattern) (ha : d374445 p = 1) (hb : d375350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339163 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d339169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371381 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d374373 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d374434 q = 1) (hb : d375341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374434, d375341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374434, d375341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d339244 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d374435 q = 1) (hb : d375342 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374435, d375342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374435, d375342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d374436 q = 1) (hb : d375343 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374436, d375343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374436, d375343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d374437 q = 1) (hb : d375344 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374437, d375344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374437, d375344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d339253 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d339257 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d371388 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d374380 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d374441 q = 1) (hb : d375346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374441, d375346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d374441, d375346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339265 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d374442 q = 1) (hb : d375347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374442, d375347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d374442, d375347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d374443 q = 1) (hb : d375348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374443, d375348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d374443, d375348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d374444 q = 1) (hb : d375349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374444, d375349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d374444, d375349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d374445 q = 1) (hb : d375350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d374445, d375350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d374445, d375350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106396 (p : Pattern) (ha : d375171 p = 1) (hb : d375357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d374380 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d374441 q = 1) (hb : d375346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374441, d375346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374441, d375346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d339265 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d374442 q = 1) (hb : d375347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374442, d375347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374442, d375347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d374443 q = 1) (hb : d375355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374443, d375355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374443, d375355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d374444 q = 1) (hb : d375356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374444, d375356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374444, d375356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375171 q = 1) (hb : d375357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d375171, d375357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375171, d375357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106397 (p : Pattern) (ha : d375181 p = 1) (hb : d375367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371424 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d374416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d375177 q = 1) (hb : d375363 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d375177, d375363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375177, d375363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d339335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d375178 q = 1) (hb : d375364 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d375178, d375364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375178, d375364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375179 q = 1) (hb : d375365 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d375179, d375365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375179, d375365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375180 q = 1) (hb : d375366 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d375180, d375366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375180, d375366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375181 q = 1) (hb : d375367 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d375181, d375367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375181, d375367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106398 (p : Pattern) (ha : d375187 p = 1) (hb : d375373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d339157 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374446 q = 1) (hb : d375351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d374446, d375351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106394 q ha hb
    | true =>
      simp only [d374446, d375351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106395 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d339272 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d374447 q = 1) (hb : d375352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d374447, d375352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374447, d375352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d375169 q = 1) (hb : d375353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375169, d375353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375169, d375353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375170 q = 1) (hb : d375354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375170, d375354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375170, d375354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375172 q = 1) (hb : d375358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d375172, d375358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375172, d375358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106396 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d339281 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d375173 q = 1) (hb : d375359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d375173, d375359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d375173, d375359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d375174 q = 1) (hb : d375360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375174, d375360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d375174, d375360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d375175 q = 1) (hb : d375361 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375175, d375361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d375175, d375361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d375176 q = 1) (hb : d375362 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d375176, d375362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375176, d375362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d375182 q = 1) (hb : d375368 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d375182, d375368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375182, d375368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106397 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d375183 q = 1) (hb : d375369 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d375183, d375369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d375183, d375369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d375184 q = 1) (hb : d375370 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375184, d375370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d375184, d375370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d375185 q = 1) (hb : d375371 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375185, d375371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d375185, d375371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d375186 q = 1) (hb : d375372 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d375186, d375372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d375186, d375372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d375187 q = 1) (hb : d375373 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d375187, d375373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d375187, d375373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106399 (p : Pattern) (ha : d375193 p = 1) (hb : d375379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375188 q = 1) (hb : d375374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d375188, d375374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375188, d375374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106398 q ha hb
  have h2 (q : Pattern) (ha : d375189 q = 1) (hb : d375375 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d375189, d375375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375189, d375375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d375190 q = 1) (hb : d375376 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d375190, d375376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375190, d375376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d375191 q = 1) (hb : d375377 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d375191, d375377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375191, d375377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d375192 q = 1) (hb : d375378 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d375192, d375378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375192, d375378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375193 q = 1) (hb : d375379 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d375193, d375379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375193, d375379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106400 (p : Pattern) (ha : d374609 p = 1) (hb : d375385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371474 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371480 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d371531 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d374604 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d374605 q = 1) (hb : d375381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374605, d375381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374605, d375381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d371566 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d374606 q = 1) (hb : d375382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374606, d375382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374606, d375382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d374607 q = 1) (hb : d375383 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374607, d375383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374607, d375383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d374608 q = 1) (hb : d375384 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374608, d375384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374608, d375384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d374609 q = 1) (hb : d375385 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d374609, d375385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374609, d375385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106401 (p : Pattern) (ha : d374619 p = 1) (hb : d375390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d371474 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371531 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d374604 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d374605 q = 1) (hb : d375381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374605, d375381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374605, d375381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d371566 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d374606 q = 1) (hb : d375382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374606, d375382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374606, d375382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d374607 q = 1) (hb : d375383 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374607, d375383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374607, d375383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d374608 q = 1) (hb : d375384 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374608, d375384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374608, d375384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d371575 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d371579 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d371581 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d374614 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d374615 q = 1) (hb : d375386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374615, d375386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d374615, d375386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d371587 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d374616 q = 1) (hb : d375387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374616, d375387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d374616, d375387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d374617 q = 1) (hb : d375388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374617, d375388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d374617, d375388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d374618 q = 1) (hb : d375389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374618, d375389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d374618, d375389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d374619 q = 1) (hb : d375390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d374619, d375390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d374619, d375390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106402 (p : Pattern) (ha : d375197 p = 1) (hb : d375397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d374614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d374615 q = 1) (hb : d375386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374615, d375386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374615, d375386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d371587 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d374616 q = 1) (hb : d375387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374616, d375387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374616, d375387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d374617 q = 1) (hb : d375395 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374617, d375395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374617, d375395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d374618 q = 1) (hb : d375396 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374618, d375396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374618, d375396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375197 q = 1) (hb : d375397 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d375197, d375397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375197, d375397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106403 (p : Pattern) (ha : d375208 p = 1) (hb : d375407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d375203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d375204 q = 1) (hb : d375403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d375204, d375403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375204, d375403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d371670 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d375205 q = 1) (hb : d375404 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d375205, d375404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375205, d375404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375206 q = 1) (hb : d375405 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d375206, d375405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375206, d375405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375207 q = 1) (hb : d375406 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d375207, d375406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375207, d375406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375208 q = 1) (hb : d375407 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d375208, d375407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375208, d375407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106404 (p : Pattern) (ha : d375214 p = 1) (hb : d375413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d371468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374620 q = 1) (hb : d375391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d374620, d375391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106400 q ha hb
    | true =>
      simp only [d374620, d375391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106401 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d374621 q = 1) (hb : d375392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d374621, d375392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374621, d375392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d375195 q = 1) (hb : d375393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375195, d375393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375195, d375393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375196 q = 1) (hb : d375394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375196, d375394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375196, d375394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375198 q = 1) (hb : d375398 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d375198, d375398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375198, d375398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106402 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d339575 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d375199 q = 1) (hb : d375399 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d375199, d375399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d375199, d375399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d375200 q = 1) (hb : d375400 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375200, d375400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d375200, d375400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d375201 q = 1) (hb : d375401 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375201, d375401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d375201, d375401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d375202 q = 1) (hb : d375402 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d375202, d375402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375202, d375402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d375209 q = 1) (hb : d375408 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d375209, d375408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375209, d375408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106403 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d339680 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d375210 q = 1) (hb : d375409 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d375210, d375409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d375210, d375409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d375211 q = 1) (hb : d375410 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375211, d375410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d375211, d375410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d375212 q = 1) (hb : d375411 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375212, d375411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d375212, d375411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d375213 q = 1) (hb : d375412 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d375213, d375412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d375213, d375412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d375214 q = 1) (hb : d375413 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d375214, d375413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d375214, d375413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106405 (p : Pattern) (ha : d375220 p = 1) (hb : d375419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375215 q = 1) (hb : d375414 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d375215, d375414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375215, d375414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106404 q ha hb
  have h2 (q : Pattern) (ha : d375216 q = 1) (hb : d375415 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d375216, d375415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375216, d375415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d375217 q = 1) (hb : d375416 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d375217, d375416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375217, d375416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d375218 q = 1) (hb : d375417 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d375218, d375417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375218, d375417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d375219 q = 1) (hb : d375418 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d375219, d375418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375219, d375418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375220 q = 1) (hb : d375419 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d375220, d375419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375220, d375419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106406 (p : Pattern) (ha : d374863 p = 1) (hb : d375426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371804 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d371866 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d374858 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d374859 q = 1) (hb : d375422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374859, d375422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374859, d375422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d371960 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d374860 q = 1) (hb : d375423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374860, d375423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d374860, d375423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d374861 q = 1) (hb : d375424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374861, d375424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374861, d375424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d374862 q = 1) (hb : d375425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374862, d375425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374862, d375425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d374863 q = 1) (hb : d375426 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d374863, d375426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374863, d375426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106407 (p : Pattern) (ha : d374873 p = 1) (hb : d375431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d371795 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d374858 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d374859 q = 1) (hb : d375422 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374859, d375422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d374859, d375422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d371960 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d374860 q = 1) (hb : d375423 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374860, d375423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d374860, d375423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d374861 q = 1) (hb : d375424 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374861, d375424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374861, d375424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d374862 q = 1) (hb : d375425 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374862, d375425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374862, d375425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d371970 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d371975 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d371977 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d374868 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d374869 q = 1) (hb : d375427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374869, d375427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d374869, d375427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d371984 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d374870 q = 1) (hb : d375428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374870, d375428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d374870, d375428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d374871 q = 1) (hb : d375429 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374871, d375429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d374871, d375429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d374872 q = 1) (hb : d375430 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374872, d375430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d374872, d375430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d374873 q = 1) (hb : d375431 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d374873, d375431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d374873, d375431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106408 (p : Pattern) (ha : d375225 p = 1) (hb : d375438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d371977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d374868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d374869 q = 1) (hb : d375427 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d374869, d375427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374869, d375427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d371984 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d374870 q = 1) (hb : d375428 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d374870, d375428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d374870, d375428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d374871 q = 1) (hb : d375436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d374871, d375436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374871, d375436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d374872 q = 1) (hb : d375437 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374872, d375437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d374872, d375437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375225 q = 1) (hb : d375438 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d375225, d375438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375225, d375438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106409 (p : Pattern) (ha : d375236 p = 1) (hb : d375448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d372099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d375231 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d375232 q = 1) (hb : d375444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d375232, d375444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375232, d375444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d372158 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d375233 q = 1) (hb : d375445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d375233, d375445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375233, d375445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375234 q = 1) (hb : d375446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d375234, d375446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375234, d375446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375235 q = 1) (hb : d375447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d375235, d375447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375235, d375447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d375236 q = 1) (hb : d375448 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d375236, d375448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375236, d375448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106410 (p : Pattern) (ha : d375242 p = 1) (hb : d375454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d371787 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d374874 q = 1) (hb : d375432 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d374874, d375432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106406 q ha hb
    | true =>
      simp only [d374874, d375432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106407 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d372002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d374875 q = 1) (hb : d375433 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d374875, d375433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d374875, d375433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d375223 q = 1) (hb : d375434 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375223, d375434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375223, d375434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375224 q = 1) (hb : d375435 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375224, d375435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375224, d375435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d375226 q = 1) (hb : d375439 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d375226, d375439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375226, d375439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106408 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d372011 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d375227 q = 1) (hb : d375440 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d375227, d375440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d375227, d375440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d375228 q = 1) (hb : d375441 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375228, d375441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d375228, d375441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d375229 q = 1) (hb : d375442 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375229, d375442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d375229, d375442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d375230 q = 1) (hb : d375443 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d375230, d375443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375230, d375443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d375237 q = 1) (hb : d375449 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d375237, d375449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375237, d375449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106409 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d372174 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d375238 q = 1) (hb : d375450 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d375238, d375450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d375238, d375450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d375239 q = 1) (hb : d375451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d375239, d375451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d375239, d375451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d375240 q = 1) (hb : d375452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d375240, d375452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d375240, d375452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d375241 q = 1) (hb : d375453 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d375241, d375453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d375241, d375453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d375242 q = 1) (hb : d375454 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d375242, d375454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d375242, d375454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106411 (p : Pattern) (ha : d375248 p = 1) (hb : d375460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375243 q = 1) (hb : d375455 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d375243, d375455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375243, d375455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106410 q ha hb
  have h2 (q : Pattern) (ha : d375244 q = 1) (hb : d375456 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d375244, d375456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375244, d375456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d375245 q = 1) (hb : d375457 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d375245, d375457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375245, d375457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d375246 q = 1) (hb : d375458 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d375246, d375458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375246, d375458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d375247 q = 1) (hb : d375459 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d375247, d375459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375247, d375459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375248 q = 1) (hb : d375460 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d375248, d375460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375248, d375460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106412 (p : Pattern) (ha : d375254 p = 1) (hb : d375551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d375194 q = 1) (hb : d375380 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d375194, d375380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106393 q hb ha
    | true =>
      simp only [d375194, d375380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106399 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d375221 q = 1) (hb : d375420 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d375221, d375420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375221, d375420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106405 q ha hb
  have h3 (q : Pattern) (ha : d375222 q = 1) (hb : d375421 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d375222, d375421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d375222, d375421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d375249 q = 1) (hb : d375461 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d375249, d375461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375249, d375461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106411 q ha hb
  have h5 (q : Pattern) (ha : d375250 q = 1) (hb : d375462 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d375250, d375462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375250, d375462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d375251 q = 1) (hb : d375463 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d375251, d375463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375251, d375463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d375505 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d375252 q = 1) (hb : d375506 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d375252, d375506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d375252, d375506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d326618 q = 1) (hb : d375546 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d326618, d375546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d326618, d375546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106387 q ha hb
  have h10 (q : Pattern) (ha : d326619 q = 1) (hb : d375547 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d326619, d375547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d326619, d375547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d326620 q = 1) (hb : d375548 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d326620, d375548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d326620, d375548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d326621 q = 1) (hb : d375549 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d326621, d375549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d326621, d375549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d375253 q = 1) (hb : d375550 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375253, d375550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d375253, d375550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d375254 q = 1) (hb : d375551 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375254, d375551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d375254, d375551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h14 p ha hb
theorem andIntro106413 (p : Pattern) (ha : d375260 p = 1) (hb : d375557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375255 q = 1) (hb : d375552 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375255, d375552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106412 q ha hb
    | true =>
      simp only [d375255, d375552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375256 q = 1) (hb : d375553 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375256, d375553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375256, d375553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375257 q = 1) (hb : d375554 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375257, d375554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375257, d375554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375258 q = 1) (hb : d375555 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375258, d375555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375258, d375555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375259 q = 1) (hb : d375556 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375259, d375556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375259, d375556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375260 q = 1) (hb : d375557 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375260, d375557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375260, d375557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106414 (p : Pattern) (ha : d375266 p = 1) (hb : d375563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375261 q = 1) (hb : d375558 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375261, d375558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106413 q ha hb
    | true =>
      simp only [d375261, d375558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375262 q = 1) (hb : d375559 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375262, d375559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375262, d375559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375263 q = 1) (hb : d375560 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375263, d375560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375263, d375560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375264 q = 1) (hb : d375561 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375264, d375561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375264, d375561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375265 q = 1) (hb : d375562 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375265, d375562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375265, d375562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375266 q = 1) (hb : d375563 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375266, d375563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375266, d375563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106415 (p : Pattern) (ha : d375272 p = 1) (hb : d375569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375267 q = 1) (hb : d375564 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375267, d375564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106414 q ha hb
    | true =>
      simp only [d375267, d375564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375268 q = 1) (hb : d375565 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375268, d375565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375268, d375565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375269 q = 1) (hb : d375566 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375269, d375566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375269, d375566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375270 q = 1) (hb : d375567 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375270, d375567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375270, d375567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375271 q = 1) (hb : d375568 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375271, d375568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375271, d375568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375272 q = 1) (hb : d375569 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375272, d375569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375272, d375569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106416 (p : Pattern) (ha : d375278 p = 1) (hb : d375575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375273 q = 1) (hb : d375570 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375273, d375570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106415 q ha hb
    | true =>
      simp only [d375273, d375570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375274 q = 1) (hb : d375571 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375274, d375571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375274, d375571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375275 q = 1) (hb : d375572 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375275, d375572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375275, d375572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375276 q = 1) (hb : d375573 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375276, d375573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375276, d375573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375277 q = 1) (hb : d375574 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375277, d375574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375277, d375574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375278 q = 1) (hb : d375575 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375278, d375575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375278, d375575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106417 (p : Pattern) (ha : d375284 p = 1) (hb : d375581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375279 q = 1) (hb : d375576 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375279, d375576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106416 q ha hb
    | true =>
      simp only [d375279, d375576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375280 q = 1) (hb : d375577 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375280, d375577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375280, d375577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375281 q = 1) (hb : d375578 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375281, d375578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375281, d375578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375282 q = 1) (hb : d375579 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375282, d375579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375282, d375579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375283 q = 1) (hb : d375580 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375283, d375580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375283, d375580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375284 q = 1) (hb : d375581 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375284, d375581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375284, d375581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106418 (p : Pattern) (ha : d375290 p = 1) (hb : d375587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375285 q = 1) (hb : d375582 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375285, d375582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106417 q ha hb
    | true =>
      simp only [d375285, d375582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375286 q = 1) (hb : d375583 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375286, d375583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375286, d375583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375287 q = 1) (hb : d375584 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375287, d375584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375287, d375584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375288 q = 1) (hb : d375585 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375288, d375585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375288, d375585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375289 q = 1) (hb : d375586 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375289, d375586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375289, d375586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375290 q = 1) (hb : d375587 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375290, d375587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375290, d375587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106419 (p : Pattern) (ha : d375296 p = 1) (hb : d375593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375291 q = 1) (hb : d375588 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375291, d375588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106418 q ha hb
    | true =>
      simp only [d375291, d375588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375292 q = 1) (hb : d375589 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375292, d375589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375292, d375589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375293 q = 1) (hb : d375590 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375293, d375590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375293, d375590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375294 q = 1) (hb : d375591 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375294, d375591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375294, d375591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375295 q = 1) (hb : d375592 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375295, d375592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375295, d375592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375296 q = 1) (hb : d375593 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375296, d375593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375296, d375593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106420 (p : Pattern) (ha : d44884 p = 1) (hb : d318725 p = 1) : d320514 p = 1 := by
  have h0 (q : Pattern) (ha : d44882 q = 1) (hb : d318724 q = 1) : d44882 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44883 q = 1) (hb : d318725 q = 1) : d179344 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44883, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d17 q = 1) (hb : d318725 q = 1) : d17 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44884 q = 1) (hb : d318725 q = 1) : d320514 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44884, d320514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44884, d320514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro106421 (p : Pattern) (ha : d44890 p = 1) (hb : d318725 p = 1) : d320520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44885 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106420 q ha hb
    | true =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44886 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44887 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d318725 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44888 q = 1) (hb : d318725 q = 1) : d320518 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44888, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44889 q = 1) (hb : d318725 q = 1) : d320519 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44889, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d318725 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d44890 q = 1) (hb : d318725 q = 1) : d320520 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44890, d320520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44890, d320520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro106422 (p : Pattern) (ha : d44896 p = 1) (hb : d318725 p = 1) : d320526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44891 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106421 q ha hb
    | true =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44892 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44893 q = 1) (hb : d318725 q = 1) : d320523 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44893, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44894 q = 1) (hb : d318725 q = 1) : d320524 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44894, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d318725 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44895 q = 1) (hb : d318725 q = 1) : d320525 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44895, d320525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44895, d320525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d318725 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44896 q = 1) (hb : d318725 q = 1) : d320526 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44896, d320526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44896, d320526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106423 (p : Pattern) (ha : d44902 p = 1) (hb : d318725 p = 1) : d320532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44897 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
    | true =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44898 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44899 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d318725 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44900 q = 1) (hb : d318725 q = 1) : d320530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44900, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44900, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d318725 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44901 q = 1) (hb : d318725 q = 1) : d320531 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44901, d320531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44901, d320531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44902 q = 1) (hb : d318725 q = 1) : d320532 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44902, d320532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44902, d320532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro106424 (p : Pattern) (ha : d44908 p = 1) (hb : d318725 p = 1) : d320538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44905 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44906 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44907 q = 1) (hb : d318725 q = 1) : d320537 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44907, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44908 q = 1) (hb : d318725 q = 1) : d320538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44908, d320538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44908, d320538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro106425 (p : Pattern) (ha : d318725 p = 1) (hb : d322010 p = 1) : d320544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d318725 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d318725 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44909 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106424 q ha hb
    | true =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322006 q = 1) : d320540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322006, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322006, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d318725 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322007 q = 1) : d320541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322007, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322007, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322008 q = 1) : d320542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322008, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322008, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318725 q = 1) (hb : d322009 q = 1) : d320543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322009, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322009, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318725 q = 1) (hb : d322010 q = 1) : d320544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322010, d320544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322010, d320544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106426 (p : Pattern) (ha : d44915 p = 1) (hb : d318725 p = 1) : d320545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44905 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44906 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44907 q = 1) (hb : d318725 q = 1) : d320537 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44907, d320537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44915 q = 1) (hb : d318725 q = 1) : d320545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44915, d320545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44915, d320545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro106427 (p : Pattern) (ha : d318725 p = 1) (hb : d322015 p = 1) : d320551 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d318725 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d318725 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44909 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106424 q ha hb
    | true =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322006 q = 1) : d320540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322006, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d322006, d320540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d318725 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322007 q = 1) : d320541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322007, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322007, d320541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322008 q = 1) : d320542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322008, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322008, d320542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318725 q = 1) (hb : d322009 q = 1) : d320543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322009, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322009, d320543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d318725 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d318725 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d318725 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d44916 q = 1) (hb : d318725 q = 1) : d320546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106426 q ha hb
    | true =>
      simp only [d44916, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d318725 q = 1) (hb : d322011 q = 1) : d320547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322011, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d322011, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d318725 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d318725 q = 1) (hb : d322012 q = 1) : d320548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322012, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322012, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d318725 q = 1) (hb : d322013 q = 1) : d320549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322013, d320549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d322013, d320549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d318725 q = 1) (hb : d322014 q = 1) : d320550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322014, d320550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d322014, d320550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d318725 q = 1) (hb : d322015 q = 1) : d320551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322015, d320551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322015, d320551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106428 (p : Pattern) (ha : d318725 p = 1) (hb : d322022 p = 1) : d320558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d318725 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44916 q = 1) (hb : d318725 q = 1) : d320546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106426 q ha hb
    | true =>
      simp only [d44916, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d318725 q = 1) (hb : d322011 q = 1) : d320547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322011, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322011, d320547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d318725 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322012 q = 1) : d320548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322012, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322012, d320548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322020 q = 1) : d320556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322020, d320556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322020, d320556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322021 q = 1) : d320557 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322021, d320557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322021, d320557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322022 q = 1) : d320558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322022, d320558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322022, d320558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106429 (p : Pattern) (ha : d44939 p = 1) (hb : d318725 p = 1) : d320569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44934 q = 1) (hb : d318725 q = 1) : d320564 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44934, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44934, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106421 q ha hb
  have h2 (q : Pattern) (ha : d44891 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106421 q ha hb
    | true =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44935 q = 1) (hb : d318725 q = 1) : d320565 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44935, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44935, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44892 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44936 q = 1) (hb : d318725 q = 1) : d320566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44936, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44936, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44937 q = 1) (hb : d318725 q = 1) : d320567 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44937, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44937, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d318725 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44938 q = 1) (hb : d318725 q = 1) : d320568 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44938, d320568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44938, d320568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d318725 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d44939 q = 1) (hb : d318725 q = 1) : d320569 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44939, d320569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44939, d320569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106430 (p : Pattern) (ha : d44945 p = 1) (hb : d318725 p = 1) : d320575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44940 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106429 q ha hb
    | true =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44941 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44942 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d318725 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44943 q = 1) (hb : d318725 q = 1) : d320573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44943, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44943, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d318725 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44944 q = 1) (hb : d318725 q = 1) : d320574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44944, d320574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44944, d320574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44945 q = 1) (hb : d318725 q = 1) : d320575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44945, d320575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44945, d320575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro106431 (p : Pattern) (ha : d44951 p = 1) (hb : d318725 p = 1) : d320581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44946 q = 1) (hb : d318725 q = 1) : d320576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106430 q ha hb
    | true =>
      simp only [d44946, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44947 q = 1) (hb : d318725 q = 1) : d320577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d318725 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44948 q = 1) (hb : d318725 q = 1) : d320578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44948, d320578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44948, d320578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44949 q = 1) (hb : d318725 q = 1) : d320579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44949, d320579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44949, d320579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44950 q = 1) (hb : d318725 q = 1) : d320580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44950, d320580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44950, d320580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44951 q = 1) (hb : d318725 q = 1) : d320581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44951, d320581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44951, d320581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro106432 (p : Pattern) (ha : d318725 p = 1) (hb : d322032 p = 1) : d320587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d318725 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44952 q = 1) (hb : d318725 q = 1) : d320582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106431 q ha hb
    | true =>
      simp only [d44952, d320582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d318725 q = 1) (hb : d322028 q = 1) : d320583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322028, d320583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d322028, d320583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d318725 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322029 q = 1) : d320584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322029, d320584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322029, d320584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322030 q = 1) : d320585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322030, d320585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322030, d320585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322031 q = 1) : d320586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322031, d320586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322031, d320586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322032 q = 1) : d320587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322032, d320587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322032, d320587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106433 (p : Pattern) (ha : d318725 p = 1) (hb : d322038 p = 1) : d320593 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d318725 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318725 q = 1) (hb : d322016 q = 1) : d320552 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322016, d320552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106425 q ha hb
    | true =>
      simp only [d322016, d320552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106427 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d318725 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318725 q = 1) (hb : d322017 q = 1) : d320553 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322017, d320553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322017, d320553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322018 q = 1) : d320554 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322018, d320554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322018, d320554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322019 q = 1) : d320555 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322019, d320555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322019, d320555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322023 q = 1) : d320559 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322023, d320559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322023, d320559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106428 q ha hb
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322024 q = 1) : d320560 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322024, d320560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322024, d320560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d318725 q = 1) (hb : d322025 q = 1) : d320561 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322025, d320561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322025, d320561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d318725 q = 1) (hb : d322026 q = 1) : d320562 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322026, d320562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322026, d320562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d318725 q = 1) (hb : d322027 q = 1) : d320563 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322027, d320563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322027, d320563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318725 q = 1) (hb : d322033 q = 1) : d320588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322033, d320588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322033, d320588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106432 q ha hb
  have h13 (q : Pattern) (ha : d318725 q = 1) (hb : d322034 q = 1) : d320589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322034, d320589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322034, d320589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d318725 q = 1) (hb : d322035 q = 1) : d320590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322035, d320590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322035, d320590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d318725 q = 1) (hb : d322036 q = 1) : d320591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322036, d320591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322036, d320591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d318725 q = 1) (hb : d322037 q = 1) : d320592 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322037, d320592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322037, d320592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d318725 q = 1) (hb : d322038 q = 1) : d320593 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322038, d320593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d322038, d320593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro106434 (p : Pattern) (ha : d44973 p = 1) (hb : d318725 p = 1) : d320603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44909 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106424 q ha hb
    | true =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44969 q = 1) (hb : d318725 q = 1) : d320599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44970 q = 1) (hb : d318725 q = 1) : d320600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44970, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44971 q = 1) (hb : d318725 q = 1) : d320601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44972 q = 1) (hb : d318725 q = 1) : d320602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44973 q = 1) (hb : d318725 q = 1) : d320603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44973, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44973, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro106435 (p : Pattern) (ha : d44980 p = 1) (hb : d318725 p = 1) : d320610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44909 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106424 q ha hb
    | true =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44969 q = 1) (hb : d318725 q = 1) : d320599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44970 q = 1) (hb : d318725 q = 1) : d320600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44970, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44971 q = 1) (hb : d318725 q = 1) : d320601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44972 q = 1) (hb : d318725 q = 1) : d320602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d318725 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44916 q = 1) (hb : d318725 q = 1) : d320546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106426 q ha hb
    | true =>
      simp only [d44916, d320546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44976 q = 1) (hb : d318725 q = 1) : d320606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44976, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44977 q = 1) (hb : d318725 q = 1) : d320607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44977, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44978 q = 1) (hb : d318725 q = 1) : d320608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44979 q = 1) (hb : d318725 q = 1) : d320609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44980 q = 1) (hb : d318725 q = 1) : d320610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44980, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44980, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro106436 (p : Pattern) (ha : d45094 p = 1) (hb : d318725 p = 1) : d320691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d318725 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44909 q = 1) (hb : d318725 q = 1) : d320539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106424 q ha hb
    | true =>
      simp only [d44909, d320539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44969 q = 1) (hb : d318725 q = 1) : d320599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44970 q = 1) (hb : d318725 q = 1) : d320600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44970, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44971 q = 1) (hb : d318725 q = 1) : d320601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44972 q = 1) (hb : d318725 q = 1) : d320602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d318725 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d45094 q = 1) (hb : d318725 q = 1) : d320691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45094, d320691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45094, d320691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106437 (p : Pattern) (ha : d44985 p = 1) (hb : d318725 p = 1) : d320615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44905 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44906 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44984 q = 1) (hb : d318725 q = 1) : d320614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44984, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44984, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44985 q = 1) (hb : d318725 q = 1) : d320615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44985, d320615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44985, d320615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro106438 (p : Pattern) (ha : d44992 p = 1) (hb : d318725 p = 1) : d320622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44905 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44990 q = 1) (hb : d318725 q = 1) : d320620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44990, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44990, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44991 q = 1) (hb : d318725 q = 1) : d320621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44991, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44991, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44992 q = 1) (hb : d318725 q = 1) : d320622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44992, d320622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44992, d320622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro106439 (p : Pattern) (ha : d44998 p = 1) (hb : d318725 p = 1) : d320626 p = 1 := by
  have h0 (q : Pattern) (ha : d44996 q = 1) (hb : d318724 q = 1) : d44996 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44997 q = 1) (hb : d318725 q = 1) : d46459 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44997, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44997, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d44882 q = 1) (hb : d318724 q = 1) : d44882 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44883 q = 1) (hb : d318725 q = 1) : d179344 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44883, d318725, d179344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44998 q = 1) (hb : d318725 q = 1) : d320626 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44998, d320626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44998, d320626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106440 (p : Pattern) (ha : d45004 p = 1) (hb : d318725 p = 1) : d320632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106439 q ha hb
    | true =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106420 q ha hb
    | true =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44887 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45002 q = 1) (hb : d318725 q = 1) : d320630 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45002, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45003 q = 1) (hb : d318725 q = 1) : d320631 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45003, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d318725 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d44888 q = 1) (hb : d318725 q = 1) : d320518 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44888, d320518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44889 q = 1) (hb : d318725 q = 1) : d320519 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44889, d320519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45004 q = 1) (hb : d318725 q = 1) : d320632 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45004, d320632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45004, d320632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro106441 (p : Pattern) (ha : d45012 p = 1) (hb : d318725 p = 1) : d320640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44885 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106420 q ha hb
    | true =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44886 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44887 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45010 q = 1) (hb : d318725 q = 1) : d320638 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45010, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45011 q = 1) (hb : d318725 q = 1) : d320639 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45011, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d318725 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d45012 q = 1) (hb : d318725 q = 1) : d320640 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45012, d320640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45012, d320640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106442 (p : Pattern) (ha : d45018 p = 1) (hb : d318725 p = 1) : d320646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45005 q = 1) (hb : d318725 q = 1) : d320633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106440 q ha hb
    | true =>
      simp only [d45005, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45006 q = 1) (hb : d318725 q = 1) : d320634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45006, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45007 q = 1) (hb : d318725 q = 1) : d320635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45007, d320635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45007, d320635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45008 q = 1) (hb : d318725 q = 1) : d320636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45008, d320636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45008, d320636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44891 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106421 q ha hb
    | true =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44892 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44893 q = 1) (hb : d318725 q = 1) : d320523 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44893, d320523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44894 q = 1) (hb : d318725 q = 1) : d320524 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44894, d320524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45009 q = 1) (hb : d318725 q = 1) : d320637 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45009, d320637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45009, d320637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45013 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
    | true =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45014 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45015 q = 1) (hb : d318725 q = 1) : d320643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45016 q = 1) (hb : d318725 q = 1) : d320644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45016, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d318725 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d45017 q = 1) (hb : d318725 q = 1) : d320645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45017, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45017, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45018 q = 1) (hb : d318725 q = 1) : d320646 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45018, d320646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45018, d320646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro106443 (p : Pattern) (ha : d45024 p = 1) (hb : d318725 p = 1) : d320652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45019 q = 1) (hb : d318725 q = 1) : d320647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106442 q ha hb
    | true =>
      simp only [d45019, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
  have h2 (q : Pattern) (ha : d45020 q = 1) (hb : d318725 q = 1) : d320648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45021 q = 1) (hb : d318725 q = 1) : d320649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44897 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
    | true =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44898 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44899 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45022 q = 1) (hb : d318725 q = 1) : d320650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45022, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d318725 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d44900 q = 1) (hb : d318725 q = 1) : d320530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44900, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44900, d320530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45023 q = 1) (hb : d318725 q = 1) : d320651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45023, d320651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45023, d320651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45024 q = 1) (hb : d318725 q = 1) : d320652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45024, d320652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45024, d320652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro106444 (p : Pattern) (ha : d45030 p = 1) (hb : d318725 p = 1) : d320658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45025 q = 1) (hb : d318725 q = 1) : d320653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45025, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106443 q ha hb
    | true =>
      simp only [d45025, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45026 q = 1) (hb : d318725 q = 1) : d320654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45026, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45026, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45027 q = 1) (hb : d318725 q = 1) : d320655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45027, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45027, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45028 q = 1) (hb : d318725 q = 1) : d320656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45028, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45028, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45029 q = 1) (hb : d318725 q = 1) : d320657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45029, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45029, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45030 q = 1) (hb : d318725 q = 1) : d320658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45030, d320658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45030, d320658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106445 (p : Pattern) (ha : d45065 p = 1) (hb : d318725 p = 1) : d320664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45062 q = 1) (hb : d318725 q = 1) : d320661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45062, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45062, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45063 q = 1) (hb : d318725 q = 1) : d320662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45063, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45063, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45064 q = 1) (hb : d318725 q = 1) : d320663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45064, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45064, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45065 q = 1) (hb : d318725 q = 1) : d320664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45065, d320664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45065, d320664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106446 (p : Pattern) (ha : d318725 p = 1) (hb : d322048 p = 1) : d320670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d318725 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44986 q = 1) (hb : d318725 q = 1) : d320616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44986, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106437 q ha hb
    | true =>
      simp only [d44986, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44987 q = 1) (hb : d318725 q = 1) : d320617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44987, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44987, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44988 q = 1) (hb : d318725 q = 1) : d320618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44988, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44988, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44989 q = 1) (hb : d318725 q = 1) : d320619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44989, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44989, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d318725 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44993 q = 1) (hb : d318725 q = 1) : d320623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44993, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106438 q ha hb
    | true =>
      simp only [d44993, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44994 q = 1) (hb : d318725 q = 1) : d320624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44994, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44994, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44995 q = 1) (hb : d318725 q = 1) : d320625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44995, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44995, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45031 q = 1) (hb : d318725 q = 1) : d320659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45031, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106444 q ha hb
    | true =>
      simp only [d45031, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106424 q ha hb
  have h11 (q : Pattern) (ha : d318725 q = 1) (hb : d322044 q = 1) : d320660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322044, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d322044, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d45066 q = 1) (hb : d318725 q = 1) : d320665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45066, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106445 q ha hb
    | true =>
      simp only [d45066, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45067 q = 1) (hb : d318725 q = 1) : d320666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45067, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45067, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d318725 q = 1) (hb : d322045 q = 1) : d320667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322045, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d322045, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d318725 q = 1) (hb : d322046 q = 1) : d320668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322046, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d322046, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318725 q = 1) (hb : d322047 q = 1) : d320669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322047, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d322047, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d318725 q = 1) (hb : d322048 q = 1) : d320670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322048, d320670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322048, d320670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro106447 (p : Pattern) (ha : d45072 p = 1) (hb : d318725 p = 1) : d320671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44905 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44906 q = 1) (hb : d318725 q = 1) : d320536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44906, d320536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44984 q = 1) (hb : d318725 q = 1) : d320614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44984, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44984, d320614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45072 q = 1) (hb : d318725 q = 1) : d320671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45072, d320671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45072, d320671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro106448 (p : Pattern) (ha : d45077 p = 1) (hb : d318725 p = 1) : d320676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d318725 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44905 q = 1) (hb : d318725 q = 1) : d320535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d320535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44990 q = 1) (hb : d318725 q = 1) : d320620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44990, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44990, d320620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44991 q = 1) (hb : d318725 q = 1) : d320621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44991, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44991, d320621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45077 q = 1) (hb : d318725 q = 1) : d320676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45077, d320676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45077, d320676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro106449 (p : Pattern) (ha : d45081 p = 1) (hb : d318725 p = 1) : d320680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45025 q = 1) (hb : d318725 q = 1) : d320653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45025, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106443 q ha hb
    | true =>
      simp only [d45025, d320653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45026 q = 1) (hb : d318725 q = 1) : d320654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45026, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45026, d320654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45027 q = 1) (hb : d318725 q = 1) : d320655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45027, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45027, d320655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45028 q = 1) (hb : d318725 q = 1) : d320656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45028, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45028, d320656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45029 q = 1) (hb : d318725 q = 1) : d320657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45029, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45029, d320657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45081 q = 1) (hb : d318725 q = 1) : d320680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45081, d320680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45081, d320680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro106450 (p : Pattern) (ha : d45086 p = 1) (hb : d318725 p = 1) : d320683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d318725 q = 1) : d320533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106423 q ha hb
    | true =>
      simp only [d44903, d320533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d318725 q = 1) : d320534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d320534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45062 q = 1) (hb : d318725 q = 1) : d320661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45062, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45062, d320661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45063 q = 1) (hb : d318725 q = 1) : d320662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45063, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45063, d320662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45064 q = 1) (hb : d318725 q = 1) : d320663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45064, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45064, d320663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45086 q = 1) (hb : d318725 q = 1) : d320683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45086, d320683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45086, d320683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106451 (p : Pattern) (ha : d318725 p = 1) (hb : d322053 p = 1) : d320689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d318725 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44986 q = 1) (hb : d318725 q = 1) : d320616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44986, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106437 q ha hb
    | true =>
      simp only [d44986, d320616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44987 q = 1) (hb : d318725 q = 1) : d320617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44987, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44987, d320617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44988 q = 1) (hb : d318725 q = 1) : d320618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44988, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44988, d320618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44989 q = 1) (hb : d318725 q = 1) : d320619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44989, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44989, d320619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d318725 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44993 q = 1) (hb : d318725 q = 1) : d320623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44993, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106438 q ha hb
    | true =>
      simp only [d44993, d320623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44994 q = 1) (hb : d318725 q = 1) : d320624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44994, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44994, d320624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44995 q = 1) (hb : d318725 q = 1) : d320625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44995, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44995, d320625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45031 q = 1) (hb : d318725 q = 1) : d320659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45031, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106444 q ha hb
    | true =>
      simp only [d45031, d320659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106424 q ha hb
  have h11 (q : Pattern) (ha : d318725 q = 1) (hb : d322044 q = 1) : d320660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322044, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d322044, d320660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d45066 q = 1) (hb : d318725 q = 1) : d320665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45066, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106445 q ha hb
    | true =>
      simp only [d45066, d320665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45067 q = 1) (hb : d318725 q = 1) : d320666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45067, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45067, d320666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d318725 q = 1) (hb : d322045 q = 1) : d320667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322045, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d322045, d320667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d318725 q = 1) (hb : d322046 q = 1) : d320668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322046, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d322046, d320668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318725 q = 1) (hb : d322047 q = 1) : d320669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322047, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d322047, d320669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d318725 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d45073 q = 1) (hb : d318725 q = 1) : d320672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45073, d320672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106447 q ha hb
    | true =>
      simp only [d45073, d320672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45074 q = 1) (hb : d318725 q = 1) : d320673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45074, d320673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45074, d320673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d45075 q = 1) (hb : d318725 q = 1) : d320674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45075, d320674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45075, d320674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d45076 q = 1) (hb : d318725 q = 1) : d320675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45076, d320675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45076, d320675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d318725 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d45078 q = 1) (hb : d318725 q = 1) : d320677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45078, d320677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106448 q ha hb
    | true =>
      simp only [d45078, d320677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d45079 q = 1) (hb : d318725 q = 1) : d320678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45079, d320678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45079, d320678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d45080 q = 1) (hb : d318725 q = 1) : d320679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45080, d320679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d45080, d320679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d45082 q = 1) (hb : d318725 q = 1) : d320681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45082, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106449 q ha hb
    | true =>
      simp only [d45082, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106426 q ha hb
  have h27 (q : Pattern) (ha : d318725 q = 1) (hb : d322049 q = 1) : d320682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322049, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d322049, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d45087 q = 1) (hb : d318725 q = 1) : d320684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45087, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106450 q ha hb
    | true =>
      simp only [d45087, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d45088 q = 1) (hb : d318725 q = 1) : d320685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45088, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d45088, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d318725 q = 1) (hb : d322050 q = 1) : d320686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322050, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d322050, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d318725 q = 1) (hb : d322051 q = 1) : d320687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322051, d320687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d322051, d320687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d318725 q = 1) (hb : d322052 q = 1) : d320688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322052, d320688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d322052, d320688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d318725 q = 1) (hb : d322053 q = 1) : d320689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322053, d320689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322053, d320689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro106452 (p : Pattern) (ha : d318725 p = 1) (hb : d322060 p = 1) : d320698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45082 q = 1) (hb : d318725 q = 1) : d320681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45082, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106449 q ha hb
    | true =>
      simp only [d45082, d320681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106426 q ha hb
  have h2 (q : Pattern) (ha : d318725 q = 1) (hb : d322049 q = 1) : d320682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322049, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322049, d320682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d45087 q = 1) (hb : d318725 q = 1) : d320684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45087, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106450 q ha hb
    | true =>
      simp only [d45087, d320684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45088 q = 1) (hb : d318725 q = 1) : d320685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45088, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45088, d320685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322050 q = 1) : d320686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322050, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322050, d320686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322058 q = 1) : d320696 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322058, d320696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322058, d320696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322059 q = 1) : d320697 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322059, d320697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322059, d320697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322060 q = 1) : d320698 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322060, d320698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322060, d320698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106453 (p : Pattern) (ha : d45117 p = 1) (hb : d318725 p = 1) : d320714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45107 q = 1) (hb : d318725 q = 1) : d320704 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45107, d320704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45107, d320704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106440 q ha hb
  have h2 (q : Pattern) (ha : d45005 q = 1) (hb : d318725 q = 1) : d320633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106440 q ha hb
    | true =>
      simp only [d45005, d320633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45108 q = 1) (hb : d318725 q = 1) : d320705 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45108, d320705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45108, d320705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45006 q = 1) (hb : d318725 q = 1) : d320634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45006, d320634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45109 q = 1) (hb : d318725 q = 1) : d320706 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45109, d320706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45109, d320706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45110 q = 1) (hb : d318725 q = 1) : d320707 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45110, d320707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45110, d320707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44934 q = 1) (hb : d318725 q = 1) : d320564 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44934, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44934, d320564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106421 q ha hb
  have h8 (q : Pattern) (ha : d44891 q = 1) (hb : d318725 q = 1) : d320521 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106421 q ha hb
    | true =>
      simp only [d44891, d320521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44935 q = 1) (hb : d318725 q = 1) : d320565 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44935, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44935, d320565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44892 q = 1) (hb : d318725 q = 1) : d320522 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44892, d320522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44936 q = 1) (hb : d318725 q = 1) : d320566 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44936, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44936, d320566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44937 q = 1) (hb : d318725 q = 1) : d320567 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44937, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44937, d320567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45111 q = 1) (hb : d318725 q = 1) : d320708 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45111, d320708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45111, d320708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45112 q = 1) (hb : d318725 q = 1) : d320709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45112, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45112, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
  have h15 (q : Pattern) (ha : d45013 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
    | true =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45113 q = 1) (hb : d318725 q = 1) : d320710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45113, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45113, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45014 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45114 q = 1) (hb : d318725 q = 1) : d320711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45114, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45114, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45115 q = 1) (hb : d318725 q = 1) : d320712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45115, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d45115, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d318725 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d45116 q = 1) (hb : d318725 q = 1) : d320713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45116, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45116, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d45117 q = 1) (hb : d318725 q = 1) : d320714 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45117, d320714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45117, d320714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro106454 (p : Pattern) (ha : d45123 p = 1) (hb : d318725 p = 1) : d320720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45118 q = 1) (hb : d318725 q = 1) : d320715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45118, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106453 q ha hb
    | true =>
      simp only [d45118, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106429 q ha hb
  have h2 (q : Pattern) (ha : d45119 q = 1) (hb : d318725 q = 1) : d320716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45119, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45119, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45120 q = 1) (hb : d318725 q = 1) : d320717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45120, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45120, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44940 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106429 q ha hb
    | true =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44941 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44942 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45121 q = 1) (hb : d318725 q = 1) : d320718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45121, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45121, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d318725 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d44943 q = 1) (hb : d318725 q = 1) : d320573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44943, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44943, d320573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45122 q = 1) (hb : d318725 q = 1) : d320719 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45122, d320719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45122, d320719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45123 q = 1) (hb : d318725 q = 1) : d320720 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45123, d320720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45123, d320720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro106455 (p : Pattern) (ha : d45129 p = 1) (hb : d318725 p = 1) : d320726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45124 q = 1) (hb : d318725 q = 1) : d320721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45124, d320721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106454 q ha hb
    | true =>
      simp only [d45124, d320721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45125 q = 1) (hb : d318725 q = 1) : d320722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45125, d320722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45125, d320722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44946 q = 1) (hb : d318725 q = 1) : d320576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106430 q ha hb
    | true =>
      simp only [d44946, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44947 q = 1) (hb : d318725 q = 1) : d320577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45126 q = 1) (hb : d318725 q = 1) : d320723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45126, d320723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45126, d320723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45127 q = 1) (hb : d318725 q = 1) : d320724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45127, d320724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45127, d320724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45128 q = 1) (hb : d318725 q = 1) : d320725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45128, d320725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45128, d320725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45129 q = 1) (hb : d318725 q = 1) : d320726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45129, d320726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45129, d320726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro106456 (p : Pattern) (ha : d45154 p = 1) (hb : d318725 p = 1) : d320732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44946 q = 1) (hb : d318725 q = 1) : d320576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106430 q ha hb
    | true =>
      simp only [d44946, d320576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44947 q = 1) (hb : d318725 q = 1) : d320577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d320577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45151 q = 1) (hb : d318725 q = 1) : d320729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45151, d320729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45151, d320729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45152 q = 1) (hb : d318725 q = 1) : d320730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45152, d320730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45152, d320730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45153 q = 1) (hb : d318725 q = 1) : d320731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45153, d320731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45153, d320731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45154 q = 1) (hb : d318725 q = 1) : d320732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45154, d320732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45154, d320732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106457 (p : Pattern) (ha : d318725 p = 1) (hb : d322070 p = 1) : d320738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45130 q = 1) (hb : d318725 q = 1) : d320727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45130, d320727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106455 q ha hb
    | true =>
      simp only [d45130, d320727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106431 q ha hb
  have h2 (q : Pattern) (ha : d318725 q = 1) (hb : d322066 q = 1) : d320728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322066, d320728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322066, d320728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d45155 q = 1) (hb : d318725 q = 1) : d320733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45155, d320733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106456 q ha hb
    | true =>
      simp only [d45155, d320733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45156 q = 1) (hb : d318725 q = 1) : d320734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45156, d320734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45156, d320734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322067 q = 1) : d320735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322067, d320735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322067, d320735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322068 q = 1) : d320736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322068, d320736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322068, d320736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322069 q = 1) : d320737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322069, d320737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322069, d320737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322070 q = 1) : d320738 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322070, d320738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322070, d320738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106458 (p : Pattern) (ha : d318725 p = 1) (hb : d322076 p = 1) : d320744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44974 q = 1) (hb : d318725 q = 1) : d320604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44974, d320604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44974, d320604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106434 q ha hb
  have h2 (q : Pattern) (ha : d44975 q = 1) (hb : d318725 q = 1) : d320605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44975, d320605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44975, d320605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44981 q = 1) (hb : d318725 q = 1) : d320611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106434 q ha hb
    | true =>
      simp only [d44981, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106435 q ha hb
  have h4 (q : Pattern) (ha : d44982 q = 1) (hb : d318725 q = 1) : d320612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44982, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44983 q = 1) (hb : d318725 q = 1) : d320613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44983, d320613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44983, d320613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322054 q = 1) : d320690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322054, d320690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106446 q ha hb
    | true =>
      simp only [d322054, d320690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106451 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d318725 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d45095 q = 1) (hb : d318725 q = 1) : d320692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45095, d320692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106436 q ha hb
    | true =>
      simp only [d45095, d320692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318725 q = 1) (hb : d322055 q = 1) : d320693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322055, d320693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322055, d320693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d318725 q = 1) (hb : d322056 q = 1) : d320694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322056, d320694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322056, d320694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d318725 q = 1) (hb : d322057 q = 1) : d320695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322057, d320695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d322057, d320695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318725 q = 1) (hb : d322061 q = 1) : d320699 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322061, d320699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322061, d320699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106452 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d318725 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d318725 q = 1) (hb : d322062 q = 1) : d320700 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322062, d320700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322062, d320700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d318725 q = 1) (hb : d322063 q = 1) : d320701 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322063, d320701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322063, d320701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d318725 q = 1) (hb : d322064 q = 1) : d320702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322064, d320702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322064, d320702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d318725 q = 1) (hb : d322065 q = 1) : d320703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322065, d320703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d322065, d320703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d318725 q = 1) (hb : d322071 q = 1) : d320739 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322071, d320739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322071, d320739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106457 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d318725 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d318725 q = 1) (hb : d322072 q = 1) : d320740 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322072, d320740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d322072, d320740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d318725 q = 1) (hb : d322073 q = 1) : d320741 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322073, d320741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d322073, d320741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d318725 q = 1) (hb : d322074 q = 1) : d320742 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322074, d320742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d322074, d320742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d318725 q = 1) (hb : d322075 q = 1) : d320743 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322075, d320743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d322075, d320743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d318725 q = 1) (hb : d322076 q = 1) : d320744 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322076, d320744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322076, d320744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro106459 (p : Pattern) (ha : d318725 p = 1) (hb : d322082 p = 1) : d320750 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d318725 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318725 q = 1) (hb : d322039 q = 1) : d320594 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322039, d320594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322039, d320594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106433 q ha hb
  have h3 (q : Pattern) (ha : d318725 q = 1) (hb : d322040 q = 1) : d320595 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322040, d320595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322040, d320595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d318725 q = 1) (hb : d322041 q = 1) : d320596 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322041, d320596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322041, d320596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322042 q = 1) : d320597 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322042, d320597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322042, d320597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322043 q = 1) : d320598 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322043, d320598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322043, d320598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322077 q = 1) : d320745 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322077, d320745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322077, d320745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106458 q ha hb
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322078 q = 1) : d320746 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322078, d320746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322078, d320746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318725 q = 1) (hb : d322079 q = 1) : d320747 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322079, d320747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322079, d320747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318725 q = 1) (hb : d322080 q = 1) : d320748 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322080, d320748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322080, d320748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d318725 q = 1) (hb : d322081 q = 1) : d320749 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322081, d320749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322081, d320749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318725 q = 1) (hb : d322082 q = 1) : d320750 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322082, d320750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322082, d320750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro106460 (p : Pattern) (ha : d45175 p = 1) (hb : d318725 p = 1) : d320753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45019 q = 1) (hb : d318725 q = 1) : d320647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106442 q ha hb
    | true =>
      simp only [d45019, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
  have h2 (q : Pattern) (ha : d45020 q = 1) (hb : d318725 q = 1) : d320648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45021 q = 1) (hb : d318725 q = 1) : d320649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44897 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
    | true =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44898 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44899 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45022 q = 1) (hb : d318725 q = 1) : d320650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45022, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45173 q = 1) (hb : d318725 q = 1) : d320751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45173, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45173, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45174 q = 1) (hb : d318725 q = 1) : d320752 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45174, d320752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45174, d320752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45175 q = 1) (hb : d318725 q = 1) : d320753 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45175, d320753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45175, d320753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro106461 (p : Pattern) (ha : d45179 p = 1) (hb : d318725 p = 1) : d320757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44897 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
    | true =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44898 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44899 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45173 q = 1) (hb : d318725 q = 1) : d320751 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45173, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45173, d320751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45178 q = 1) (hb : d318725 q = 1) : d320756 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45178, d320756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45178, d320756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45179 q = 1) (hb : d318725 q = 1) : d320757 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45179, d320757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45179, d320757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro106462 (p : Pattern) (ha : d45185 p = 1) (hb : d318725 p = 1) : d320763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45184 q = 1) (hb : d318725 q = 1) : d320762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45184, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45184, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45185 q = 1) (hb : d318725 q = 1) : d320763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45185, d320763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45185, d320763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106463 (p : Pattern) (ha : d45189 p = 1) (hb : d318725 p = 1) : d320767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45188 q = 1) (hb : d318725 q = 1) : d320766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45188, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45188, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45189 q = 1) (hb : d318725 q = 1) : d320767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45189, d320767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45189, d320767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106464 (p : Pattern) (ha : d45195 p = 1) (hb : d318725 p = 1) : d320773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d318725 q = 1) : d320768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106462 q ha hb
    | true =>
      simp only [d45190, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106463 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d318725 q = 1) : d320769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d318725 q = 1) : d320770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d318725 q = 1) : d320771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d318725 q = 1) : d320772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45195 q = 1) (hb : d318725 q = 1) : d320773 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45195, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45195, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106465 (p : Pattern) (ha : d45198 p = 1) (hb : d318725 p = 1) : d320776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45184 q = 1) (hb : d318725 q = 1) : d320762 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45184, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45184, d320762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45198 q = 1) (hb : d318725 q = 1) : d320776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45198, d320776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45198, d320776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro106466 (p : Pattern) (ha : d45199 p = 1) (hb : d318725 p = 1) : d320777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45188 q = 1) (hb : d318725 q = 1) : d320766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45188, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45188, d320766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45199 q = 1) (hb : d318725 q = 1) : d320777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45199, d320777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45199, d320777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106467 (p : Pattern) (ha : d45205 p = 1) (hb : d318725 p = 1) : d320783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d318725 q = 1) : d320768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106462 q ha hb
    | true =>
      simp only [d45190, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106463 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d318725 q = 1) : d320769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d318725 q = 1) : d320770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d318725 q = 1) : d320771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d318725 q = 1) : d320772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45200 q = 1) (hb : d318725 q = 1) : d320778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106465 q ha hb
    | true =>
      simp only [d45200, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106466 q ha hb
  have h7 (q : Pattern) (ha : d45201 q = 1) (hb : d318725 q = 1) : d320779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45201, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45202 q = 1) (hb : d318725 q = 1) : d320780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45202, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45203 q = 1) (hb : d318725 q = 1) : d320781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45204 q = 1) (hb : d318725 q = 1) : d320782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45205 q = 1) (hb : d318725 q = 1) : d320783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45205, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45205, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106468 (p : Pattern) (ha : d45363 p = 1) (hb : d318725 p = 1) : d320887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d318725 q = 1) : d320768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106462 q ha hb
    | true =>
      simp only [d45190, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106463 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d318725 q = 1) : d320769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d318725 q = 1) : d320770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d318725 q = 1) : d320771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d318725 q = 1) : d320772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45358 q = 1) (hb : d318725 q = 1) : d320882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45358, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106463 q ha hb
    | true =>
      simp only [d45358, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45359 q = 1) (hb : d318725 q = 1) : d320883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45359, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45359, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45360 q = 1) (hb : d318725 q = 1) : d320884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45360, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45360, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45361 q = 1) (hb : d318725 q = 1) : d320885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45361, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45361, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45362 q = 1) (hb : d318725 q = 1) : d320886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45362, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45362, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45363 q = 1) (hb : d318725 q = 1) : d320887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45363, d320887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45363, d320887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106469 (p : Pattern) (ha : d45369 p = 1) (hb : d318725 p = 1) : d320893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45358 q = 1) (hb : d318725 q = 1) : d320882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45358, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106463 q ha hb
    | true =>
      simp only [d45358, d320882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45359 q = 1) (hb : d318725 q = 1) : d320883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45359, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45359, d320883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45360 q = 1) (hb : d318725 q = 1) : d320884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45360, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45360, d320884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45361 q = 1) (hb : d318725 q = 1) : d320885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45361, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45361, d320885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45362 q = 1) (hb : d318725 q = 1) : d320886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45362, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45362, d320886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45364 q = 1) (hb : d318725 q = 1) : d320888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45364, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106466 q ha hb
    | true =>
      simp only [d45364, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45365 q = 1) (hb : d318725 q = 1) : d320889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45365, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45365, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45366 q = 1) (hb : d318725 q = 1) : d320890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45366, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45366, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45367 q = 1) (hb : d318725 q = 1) : d320891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45367, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45367, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45368 q = 1) (hb : d318725 q = 1) : d320892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45368, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45368, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45369 q = 1) (hb : d318725 q = 1) : d320893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45369, d320893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45369, d320893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro106470 (p : Pattern) (ha : d45378 p = 1) (hb : d318725 p = 1) : d320902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45364 q = 1) (hb : d318725 q = 1) : d320888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45364, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106466 q ha hb
    | true =>
      simp only [d45364, d320888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45365 q = 1) (hb : d318725 q = 1) : d320889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45365, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45365, d320889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45366 q = 1) (hb : d318725 q = 1) : d320890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45366, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45366, d320890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45367 q = 1) (hb : d318725 q = 1) : d320891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45367, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45367, d320891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45368 q = 1) (hb : d318725 q = 1) : d320892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45368, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45368, d320892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45378 q = 1) (hb : d318725 q = 1) : d320902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45378, d320902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45378, d320902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106471 (p : Pattern) (ha : d45421 p = 1) (hb : d318725 p = 1) : d320945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44940 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106429 q ha hb
    | true =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44941 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44942 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45411 q = 1) (hb : d318725 q = 1) : d320935 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45411, d320935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45411, d320935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45420 q = 1) (hb : d318725 q = 1) : d320944 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45420, d320944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45420, d320944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45421 q = 1) (hb : d318725 q = 1) : d320945 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45421, d320945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45421, d320945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro106472 (p : Pattern) (ha : d45477 p = 1) (hb : d318725 p = 1) : d320968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45422 q = 1) (hb : d318725 q = 1) : d320946 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45422, d320946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106471 q ha hb
    | true =>
      simp only [d45422, d320946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45423 q = 1) (hb : d318725 q = 1) : d320947 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45423, d320947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45423, d320947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45474 q = 1) (hb : d318725 q = 1) : d320965 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45474, d320965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45474, d320965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45475 q = 1) (hb : d318725 q = 1) : d320966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45475, d320966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45475, d320966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45476 q = 1) (hb : d318725 q = 1) : d320967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45476, d320967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45476, d320967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45477 q = 1) (hb : d318725 q = 1) : d320968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45477, d320968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45477, d320968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106473 (p : Pattern) (ha : d45483 p = 1) (hb : d318725 p = 1) : d320974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45478 q = 1) (hb : d318725 q = 1) : d320969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45478, d320969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106472 q ha hb
    | true =>
      simp only [d45478, d320969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45479 q = 1) (hb : d318725 q = 1) : d320970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45479, d320970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45479, d320970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45480 q = 1) (hb : d318725 q = 1) : d320971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45480, d320971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45480, d320971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45481 q = 1) (hb : d318725 q = 1) : d320972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45481, d320972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45481, d320972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45482 q = 1) (hb : d318725 q = 1) : d320973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45482, d320973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45482, d320973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45483 q = 1) (hb : d318725 q = 1) : d320974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45483, d320974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45483, d320974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106474 (p : Pattern) (ha : d45210 p = 1) (hb : d318725 p = 1) : d320788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45209 q = 1) (hb : d318725 q = 1) : d320787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45209, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45209, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45210 q = 1) (hb : d318725 q = 1) : d320788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45210, d320788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45210, d320788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106475 (p : Pattern) (ha : d45212 p = 1) (hb : d318725 p = 1) : d320790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45211 q = 1) (hb : d318725 q = 1) : d320789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45211, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45211, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45212 q = 1) (hb : d318725 q = 1) : d320790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45212, d320790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45212, d320790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106476 (p : Pattern) (ha : d45219 p = 1) (hb : d318725 p = 1) : d320797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45217 q = 1) (hb : d318725 q = 1) : d320795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45217, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45217, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45218 q = 1) (hb : d318725 q = 1) : d320796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45218, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45218, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45219 q = 1) (hb : d318725 q = 1) : d320797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45219, d320797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45219, d320797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106477 (p : Pattern) (ha : d45222 p = 1) (hb : d318725 p = 1) : d320800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45220 q = 1) (hb : d318725 q = 1) : d320798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45220, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45220, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45221 q = 1) (hb : d318725 q = 1) : d320799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45221, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45221, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45222 q = 1) (hb : d318725 q = 1) : d320800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45222, d320800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45222, d320800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106478 (p : Pattern) (ha : d45227 p = 1) (hb : d318725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44882 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d45226 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45226, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45226, d318725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d45227 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro106479 (p : Pattern) (ha : d45234 p = 1) (hb : d318725 p = 1) : d320806 p = 1 := by
  have h0 (q : Pattern) (ha : d44996 q = 1) (hb : d318724 q = 1) : d44996 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d45231 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d45232 q = 1) (hb : d318725 q = 1) : d46459 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45232, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45232, d318725, d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d45231 q = 1) (hb : d318724 q = 1) : d45231 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45233 q = 1) (hb : d318725 q = 1) : d320805 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45233, d318725, d320805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45233, d318725, d320805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d45234 q = 1) (hb : d318725 q = 1) : d320806 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45234, d320806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45234, d320806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106480 (p : Pattern) (ha : d45240 p = 1) (hb : d318725 p = 1) : d320812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45228 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106478 q ha hb
    | true =>
      simp only [d45228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45229 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44999 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106439 q ha hb
    | true =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45000 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45230 q = 1) (hb : d318725 q = 1) : d320804 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45230, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45230, d320804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45235 q = 1) (hb : d318725 q = 1) : d320807 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45235, d320807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106479 q ha hb
    | true =>
      simp only [d45235, d320807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45236 q = 1) (hb : d318725 q = 1) : d320808 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45236, d320808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45236, d320808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106420 q ha hb
    | true =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45237 q = 1) (hb : d318725 q = 1) : d320809 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45237, d320809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45237, d320809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45238 q = 1) (hb : d318725 q = 1) : d320810 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45238, d320810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45238, d320810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45239 q = 1) (hb : d318725 q = 1) : d320811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45239, d320811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45239, d320811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45001 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44887 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45002 q = 1) (hb : d318725 q = 1) : d320630 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45002, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45003 q = 1) (hb : d318725 q = 1) : d320631 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45003, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45240 q = 1) (hb : d318725 q = 1) : d320812 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45240, d320812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45240, d320812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro106481 (p : Pattern) (ha : d45245 p = 1) (hb : d318725 p = 1) : d320817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106439 q ha hb
    | true =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106420 q ha hb
    | true =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44887 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45002 q = 1) (hb : d318725 q = 1) : d320630 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45002, d320630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45003 q = 1) (hb : d318725 q = 1) : d320631 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45003, d320631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45010 q = 1) (hb : d318725 q = 1) : d320638 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45010, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45011 q = 1) (hb : d318725 q = 1) : d320639 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45011, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45245 q = 1) (hb : d318725 q = 1) : d320817 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45245, d320817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45245, d320817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro106482 (p : Pattern) (ha : d45253 p = 1) (hb : d318725 p = 1) : d320825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d318725 q = 1) : d320627 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106439 q ha hb
    | true =>
      simp only [d44999, d320627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d318725 q = 1) : d320628 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d320628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d318725 q = 1) : d320515 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106420 q ha hb
    | true =>
      simp only [d44885, d320515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d318725 q = 1) : d320516 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d320516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d318725 q = 1) : d320629 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d320629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45251 q = 1) (hb : d318725 q = 1) : d320823 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45251, d320823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45251, d320823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45252 q = 1) (hb : d318725 q = 1) : d320824 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45252, d320824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45252, d320824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d318725 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d44887 q = 1) (hb : d318725 q = 1) : d320517 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d320517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45010 q = 1) (hb : d318725 q = 1) : d320638 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45010, d320638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45011 q = 1) (hb : d318725 q = 1) : d320639 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45011, d320639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45253 q = 1) (hb : d318725 q = 1) : d320825 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45253, d320825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45253, d320825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro106483 (p : Pattern) (ha : d45259 p = 1) (hb : d318725 p = 1) : d320831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45241 q = 1) (hb : d318725 q = 1) : d320813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45241, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106480 q ha hb
    | true =>
      simp only [d45241, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45242 q = 1) (hb : d318725 q = 1) : d320814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45242, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45242, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45243 q = 1) (hb : d318725 q = 1) : d320815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45243, d320815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45243, d320815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45244 q = 1) (hb : d318725 q = 1) : d320816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45244, d320816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45244, d320816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45246 q = 1) (hb : d318725 q = 1) : d320818 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45246, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106481 q ha hb
    | true =>
      simp only [d45246, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45247 q = 1) (hb : d318725 q = 1) : d320819 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45247, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45247, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45248 q = 1) (hb : d318725 q = 1) : d320820 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45248, d320820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45248, d320820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45249 q = 1) (hb : d318725 q = 1) : d320821 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45249, d320821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45249, d320821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45250 q = 1) (hb : d318725 q = 1) : d320822 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45250, d320822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45250, d320822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45254 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106482 q ha hb
    | true =>
      simp only [d45254, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45255 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45255, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45256 q = 1) (hb : d318725 q = 1) : d320828 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45256, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45256, d320828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45257 q = 1) (hb : d318725 q = 1) : d320829 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45257, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45257, d320829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45013 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
    | true =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45014 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45015 q = 1) (hb : d318725 q = 1) : d320643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45016 q = 1) (hb : d318725 q = 1) : d320644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45016, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45258 q = 1) (hb : d318725 q = 1) : d320830 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45258, d320830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45258, d320830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45259 q = 1) (hb : d318725 q = 1) : d320831 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45259, d320831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45259, d320831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro106484 (p : Pattern) (ha : d45263 p = 1) (hb : d318725 p = 1) : d320835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45013 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
    | true =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45014 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45015 q = 1) (hb : d318725 q = 1) : d320643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d320643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45016 q = 1) (hb : d318725 q = 1) : d320644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45016, d320644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d318725 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d45017 q = 1) (hb : d318725 q = 1) : d320645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45017, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45017, d320645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d318725 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d45263 q = 1) (hb : d318725 q = 1) : d320835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45263, d320835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45263, d320835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106485 (p : Pattern) (ha : d45269 p = 1) (hb : d318725 p = 1) : d320841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45260 q = 1) (hb : d318725 q = 1) : d320832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45260, d320832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106483 q ha hb
    | true =>
      simp only [d45260, d320832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106442 q ha hb
  have h2 (q : Pattern) (ha : d45261 q = 1) (hb : d318725 q = 1) : d320833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45261, d320833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45261, d320833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45262 q = 1) (hb : d318725 q = 1) : d320834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45262, d320834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45262, d320834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45264 q = 1) (hb : d318725 q = 1) : d320836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45264, d320836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106442 q ha hb
    | true =>
      simp only [d45264, d320836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106484 q ha hb
  have h5 (q : Pattern) (ha : d45265 q = 1) (hb : d318725 q = 1) : d320837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45265, d320837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45265, d320837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45266 q = 1) (hb : d318725 q = 1) : d320838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45266, d320838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45266, d320838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45267 q = 1) (hb : d318725 q = 1) : d320839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45267, d320839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45267, d320839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45019 q = 1) (hb : d318725 q = 1) : d320647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106442 q ha hb
    | true =>
      simp only [d45019, d320647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
  have h9 (q : Pattern) (ha : d45020 q = 1) (hb : d318725 q = 1) : d320648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d320648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45021 q = 1) (hb : d318725 q = 1) : d320649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d320649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d318725 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d44897 q = 1) (hb : d318725 q = 1) : d320527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106422 q ha hb
    | true =>
      simp only [d44897, d320527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44898 q = 1) (hb : d318725 q = 1) : d320528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d320528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44899 q = 1) (hb : d318725 q = 1) : d320529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d320529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45022 q = 1) (hb : d318725 q = 1) : d320650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45022, d320650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45268 q = 1) (hb : d318725 q = 1) : d320840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45268, d320840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45268, d320840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45269 q = 1) (hb : d318725 q = 1) : d320841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45269, d320841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45269, d320841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro106486 (p : Pattern) (ha : d45275 p = 1) (hb : d318725 p = 1) : d320847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45270 q = 1) (hb : d318725 q = 1) : d320842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45270, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106485 q ha hb
    | true =>
      simp only [d45270, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45271 q = 1) (hb : d318725 q = 1) : d320843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45271, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45271, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45272 q = 1) (hb : d318725 q = 1) : d320844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45272, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45272, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45273 q = 1) (hb : d318725 q = 1) : d320845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45273, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45273, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45274 q = 1) (hb : d318725 q = 1) : d320846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45274, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45274, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45275 q = 1) (hb : d318725 q = 1) : d320847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45275, d320847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45275, d320847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106487 (p : Pattern) (ha : d45326 p = 1) (hb : d318725 p = 1) : d320853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45323 q = 1) (hb : d318725 q = 1) : d320850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45323, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45323, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45324 q = 1) (hb : d318725 q = 1) : d320851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45324, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45324, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45325 q = 1) (hb : d318725 q = 1) : d320852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45325, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45325, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45326 q = 1) (hb : d318725 q = 1) : d320853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45326, d320853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45326, d320853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro106488 (p : Pattern) (ha : d318725 p = 1) (hb : d322087 p = 1) : d320859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45213 q = 1) (hb : d318725 q = 1) : d320791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45213, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106474 q ha hb
    | true =>
      simp only [d45213, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106475 q ha hb
  have h2 (q : Pattern) (ha : d45214 q = 1) (hb : d318725 q = 1) : d320792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45214, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45214, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45215 q = 1) (hb : d318725 q = 1) : d320793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45215, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45215, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45216 q = 1) (hb : d318725 q = 1) : d320794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45216, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45216, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45223 q = 1) (hb : d318725 q = 1) : d320801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45223, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106476 q ha hb
    | true =>
      simp only [d45223, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106477 q ha hb
  have h6 (q : Pattern) (ha : d45224 q = 1) (hb : d318725 q = 1) : d320802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45224, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45224, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45225 q = 1) (hb : d318725 q = 1) : d320803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45225, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45225, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45276 q = 1) (hb : d318725 q = 1) : d320848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45276, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106486 q ha hb
    | true =>
      simp only [d45276, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106462 q ha hb
  have h9 (q : Pattern) (ha : d318725 q = 1) (hb : d322083 q = 1) : d320849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322083, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322083, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d45327 q = 1) (hb : d318725 q = 1) : d320854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45327, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106487 q ha hb
    | true =>
      simp only [d45327, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45328 q = 1) (hb : d318725 q = 1) : d320855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45328, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45328, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d318725 q = 1) (hb : d322084 q = 1) : d320856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322084, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322084, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d318725 q = 1) (hb : d322085 q = 1) : d320857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322085, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322085, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d318725 q = 1) (hb : d322086 q = 1) : d320858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322086, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322086, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d318725 q = 1) (hb : d322087 q = 1) : d320859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322087, d320859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322087, d320859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro106489 (p : Pattern) (ha : d45333 p = 1) (hb : d318725 p = 1) : d320860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d318725 q = 1) : d320761 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d320761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45209 q = 1) (hb : d318725 q = 1) : d320787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45209, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45209, d320787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45333 q = 1) (hb : d318725 q = 1) : d320860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45333, d320860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45333, d320860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro106490 (p : Pattern) (ha : d45334 p = 1) (hb : d318725 p = 1) : d320861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d318725 q = 1) : d320765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d320765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45211 q = 1) (hb : d318725 q = 1) : d320789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45211, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45211, d320789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45334 q = 1) (hb : d318725 q = 1) : d320861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45334, d320861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45334, d320861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106491 (p : Pattern) (ha : d45339 p = 1) (hb : d318725 p = 1) : d320866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d318725 q = 1) : d320760 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d320760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45217 q = 1) (hb : d318725 q = 1) : d320795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45217, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45217, d320795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45218 q = 1) (hb : d318725 q = 1) : d320796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45218, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45218, d320796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45339 q = 1) (hb : d318725 q = 1) : d320866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45339, d320866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45339, d320866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro106492 (p : Pattern) (ha : d45340 p = 1) (hb : d318725 p = 1) : d320867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d318725 q = 1) : d320758 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106461 q ha hb
    | true =>
      simp only [d45180, d320758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d318725 q = 1) : d320759 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d320759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d318725 q = 1) : d320764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d320764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45220 q = 1) (hb : d318725 q = 1) : d320798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45220, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45220, d320798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45221 q = 1) (hb : d318725 q = 1) : d320799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45221, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45221, d320799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45340 q = 1) (hb : d318725 q = 1) : d320867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45340, d320867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45340, d320867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106493 (p : Pattern) (ha : d45344 p = 1) (hb : d318725 p = 1) : d320871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45270 q = 1) (hb : d318725 q = 1) : d320842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45270, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106485 q ha hb
    | true =>
      simp only [d45270, d320842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45271 q = 1) (hb : d318725 q = 1) : d320843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45271, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45271, d320843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45272 q = 1) (hb : d318725 q = 1) : d320844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45272, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45272, d320844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45273 q = 1) (hb : d318725 q = 1) : d320845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45273, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45273, d320845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45274 q = 1) (hb : d318725 q = 1) : d320846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45274, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45274, d320846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45344 q = 1) (hb : d318725 q = 1) : d320871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45344, d320871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45344, d320871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro106494 (p : Pattern) (ha : d45350 p = 1) (hb : d318725 p = 1) : d320874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d318725 q = 1) : d320754 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106460 q ha hb
    | true =>
      simp only [d45176, d320754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d318725 q = 1) : d320755 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d320755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45323 q = 1) (hb : d318725 q = 1) : d320850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45323, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45323, d320850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45324 q = 1) (hb : d318725 q = 1) : d320851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45324, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45324, d320851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45325 q = 1) (hb : d318725 q = 1) : d320852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45325, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45325, d320852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45350 q = 1) (hb : d318725 q = 1) : d320874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45350, d320874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45350, d320874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro106495 (p : Pattern) (ha : d318725 p = 1) (hb : d322092 p = 1) : d320880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45213 q = 1) (hb : d318725 q = 1) : d320791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45213, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106474 q ha hb
    | true =>
      simp only [d45213, d320791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106475 q ha hb
  have h2 (q : Pattern) (ha : d45214 q = 1) (hb : d318725 q = 1) : d320792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45214, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45214, d320792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45215 q = 1) (hb : d318725 q = 1) : d320793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45215, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45215, d320793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45216 q = 1) (hb : d318725 q = 1) : d320794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45216, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45216, d320794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45223 q = 1) (hb : d318725 q = 1) : d320801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45223, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106476 q ha hb
    | true =>
      simp only [d45223, d320801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106477 q ha hb
  have h6 (q : Pattern) (ha : d45224 q = 1) (hb : d318725 q = 1) : d320802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45224, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45224, d320802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45225 q = 1) (hb : d318725 q = 1) : d320803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45225, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45225, d320803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45276 q = 1) (hb : d318725 q = 1) : d320848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45276, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106486 q ha hb
    | true =>
      simp only [d45276, d320848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106462 q ha hb
  have h9 (q : Pattern) (ha : d318725 q = 1) (hb : d322083 q = 1) : d320849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322083, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322083, d320849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d45327 q = 1) (hb : d318725 q = 1) : d320854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45327, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106487 q ha hb
    | true =>
      simp only [d45327, d320854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45328 q = 1) (hb : d318725 q = 1) : d320855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45328, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45328, d320855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d318725 q = 1) (hb : d322084 q = 1) : d320856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322084, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322084, d320856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d318725 q = 1) (hb : d322085 q = 1) : d320857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322085, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322085, d320857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d318725 q = 1) (hb : d322086 q = 1) : d320858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322086, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322086, d320858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45335 q = 1) (hb : d318725 q = 1) : d320862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45335, d320862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106489 q ha hb
    | true =>
      simp only [d45335, d320862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106490 q ha hb
  have h16 (q : Pattern) (ha : d45336 q = 1) (hb : d318725 q = 1) : d320863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45336, d320863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45336, d320863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45337 q = 1) (hb : d318725 q = 1) : d320864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45337, d320864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45337, d320864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45338 q = 1) (hb : d318725 q = 1) : d320865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45338, d320865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45338, d320865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45341 q = 1) (hb : d318725 q = 1) : d320868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45341, d320868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106491 q ha hb
    | true =>
      simp only [d45341, d320868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106492 q ha hb
  have h20 (q : Pattern) (ha : d45342 q = 1) (hb : d318725 q = 1) : d320869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45342, d320869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45342, d320869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d45343 q = 1) (hb : d318725 q = 1) : d320870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45343, d320870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d45343, d320870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d45345 q = 1) (hb : d318725 q = 1) : d320872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45345, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106493 q ha hb
    | true =>
      simp only [d45345, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106465 q ha hb
  have h23 (q : Pattern) (ha : d318725 q = 1) (hb : d322088 q = 1) : d320873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322088, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d322088, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d45351 q = 1) (hb : d318725 q = 1) : d320875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45351, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106494 q ha hb
    | true =>
      simp only [d45351, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d45352 q = 1) (hb : d318725 q = 1) : d320876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45352, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d45352, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d318725 q = 1) (hb : d322089 q = 1) : d320877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322089, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d322089, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d318725 q = 1) (hb : d322090 q = 1) : d320878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322090, d320878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d322090, d320878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d318725 q = 1) (hb : d322091 q = 1) : d320879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322091, d320879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d322091, d320879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d318725 q = 1) (hb : d322092 q = 1) : d320880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322092, d320880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322092, d320880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro106496 (p : Pattern) (ha : d318725 p = 1) (hb : d322099 p = 1) : d320900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45345 q = 1) (hb : d318725 q = 1) : d320872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45345, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106493 q ha hb
    | true =>
      simp only [d45345, d320872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106465 q ha hb
  have h2 (q : Pattern) (ha : d318725 q = 1) (hb : d322088 q = 1) : d320873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322088, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322088, d320873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d45351 q = 1) (hb : d318725 q = 1) : d320875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45351, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106494 q ha hb
    | true =>
      simp only [d45351, d320875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45352 q = 1) (hb : d318725 q = 1) : d320876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45352, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45352, d320876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318725 q = 1) (hb : d322089 q = 1) : d320877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322089, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322089, d320877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d318725 q = 1) (hb : d322097 q = 1) : d320898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322097, d320898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322097, d320898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318725 q = 1) (hb : d322098 q = 1) : d320899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322098, d320899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322098, d320899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318725 q = 1) (hb : d322099 q = 1) : d320900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322099, d320900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322099, d320900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro106497 (p : Pattern) (ha : d45398 p = 1) (hb : d318725 p = 1) : d320922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45384 q = 1) (hb : d318725 q = 1) : d320908 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45384, d320908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45384, d320908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106480 q ha hb
  have h2 (q : Pattern) (ha : d45241 q = 1) (hb : d318725 q = 1) : d320813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45241, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106480 q ha hb
    | true =>
      simp only [d45241, d320813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45385 q = 1) (hb : d318725 q = 1) : d320909 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45385, d320909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45385, d320909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45242 q = 1) (hb : d318725 q = 1) : d320814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45242, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45242, d320814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45386 q = 1) (hb : d318725 q = 1) : d320910 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45386, d320910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45386, d320910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45387 q = 1) (hb : d318725 q = 1) : d320911 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45387, d320911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45387, d320911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45388 q = 1) (hb : d318725 q = 1) : d320912 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45388, d320912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45388, d320912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106481 q ha hb
  have h8 (q : Pattern) (ha : d45246 q = 1) (hb : d318725 q = 1) : d320818 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45246, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106481 q ha hb
    | true =>
      simp only [d45246, d320818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45389 q = 1) (hb : d318725 q = 1) : d320913 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45389, d320913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45389, d320913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45247 q = 1) (hb : d318725 q = 1) : d320819 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45247, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45247, d320819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45390 q = 1) (hb : d318725 q = 1) : d320914 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45390, d320914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45390, d320914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45391 q = 1) (hb : d318725 q = 1) : d320915 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45391, d320915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45391, d320915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45392 q = 1) (hb : d318725 q = 1) : d320916 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45392, d320916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45392, d320916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45393 q = 1) (hb : d318725 q = 1) : d320917 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45393, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45393, d320917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106482 q ha hb
  have h15 (q : Pattern) (ha : d45254 q = 1) (hb : d318725 q = 1) : d320826 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106482 q ha hb
    | true =>
      simp only [d45254, d320826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45394 q = 1) (hb : d318725 q = 1) : d320918 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45394, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45394, d320918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45255 q = 1) (hb : d318725 q = 1) : d320827 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45255, d320827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45395 q = 1) (hb : d318725 q = 1) : d320919 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45395, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45395, d320919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45396 q = 1) (hb : d318725 q = 1) : d320920 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45396, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d45396, d320920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d45112 q = 1) (hb : d318725 q = 1) : d320709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45112, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45112, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
  have h21 (q : Pattern) (ha : d45013 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
    | true =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d45113 q = 1) (hb : d318725 q = 1) : d320710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45113, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d45113, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d45014 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d45114 q = 1) (hb : d318725 q = 1) : d320711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45114, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d45114, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d45115 q = 1) (hb : d318725 q = 1) : d320712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45115, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d45115, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d45397 q = 1) (hb : d318725 q = 1) : d320921 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45397, d320921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45397, d320921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d45398 q = 1) (hb : d318725 q = 1) : d320922 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45398, d320922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45398, d320922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro106498 (p : Pattern) (ha : d45402 p = 1) (hb : d318725 p = 1) : d320926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45112 q = 1) (hb : d318725 q = 1) : d320709 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45112, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45112, d320709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
  have h2 (q : Pattern) (ha : d45013 q = 1) (hb : d318725 q = 1) : d320641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106441 q ha hb
    | true =>
      simp only [d45013, d320641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45113 q = 1) (hb : d318725 q = 1) : d320710 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45113, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45113, d320710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45014 q = 1) (hb : d318725 q = 1) : d320642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45014, d320642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45114 q = 1) (hb : d318725 q = 1) : d320711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45114, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45114, d320711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45115 q = 1) (hb : d318725 q = 1) : d320712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45115, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45115, d320712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d318725 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d45116 q = 1) (hb : d318725 q = 1) : d320713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45116, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45116, d320713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d318725 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d45402 q = 1) (hb : d318725 q = 1) : d320926 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45402, d320926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45402, d320926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro106499 (p : Pattern) (ha : d45408 p = 1) (hb : d318725 p = 1) : d320932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318725 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45399 q = 1) (hb : d318725 q = 1) : d320923 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45399, d320923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106497 q ha hb
    | true =>
      simp only [d45399, d320923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106453 q ha hb
  have h2 (q : Pattern) (ha : d45400 q = 1) (hb : d318725 q = 1) : d320924 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45400, d320924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45400, d320924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45401 q = 1) (hb : d318725 q = 1) : d320925 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45401, d320925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45401, d320925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45403 q = 1) (hb : d318725 q = 1) : d320927 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45403, d320927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106453 q ha hb
    | true =>
      simp only [d45403, d320927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106498 q ha hb
  have h5 (q : Pattern) (ha : d45404 q = 1) (hb : d318725 q = 1) : d320928 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45404, d320928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45404, d320928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45405 q = 1) (hb : d318725 q = 1) : d320929 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45405, d320929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45405, d320929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45406 q = 1) (hb : d318725 q = 1) : d320930 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45406, d320930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45406, d320930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45118 q = 1) (hb : d318725 q = 1) : d320715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45118, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106453 q ha hb
    | true =>
      simp only [d45118, d320715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106429 q ha hb
  have h9 (q : Pattern) (ha : d45119 q = 1) (hb : d318725 q = 1) : d320716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45119, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45119, d320716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45120 q = 1) (hb : d318725 q = 1) : d320717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45120, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45120, d320717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d318725 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d44940 q = 1) (hb : d318725 q = 1) : d320570 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106429 q ha hb
    | true =>
      simp only [d44940, d320570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44941 q = 1) (hb : d318725 q = 1) : d320571 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d320571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44942 q = 1) (hb : d318725 q = 1) : d320572 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d320572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45121 q = 1) (hb : d318725 q = 1) : d320718 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45121, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45121, d320718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45407 q = 1) (hb : d318725 q = 1) : d320931 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45407, d320931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45407, d320931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45408 q = 1) (hb : d318725 q = 1) : d320932 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45408, d320932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45408, d320932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
end NetHack.Soko22Hazard87
