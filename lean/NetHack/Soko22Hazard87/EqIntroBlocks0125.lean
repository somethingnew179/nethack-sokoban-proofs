import NetHack.Soko22Hazard87.EqIntroBlocks0124
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro31250 (p : Pattern) (selected : d301766 p = 0) : d303438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301743 q = 0) : d303415 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301743, d303415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301743, d303415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31019 q selected
  have h2 (q : Pattern) (selected : d301744 q = 0) : d303416 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301744, d303416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301744, d303416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301745 q = 0) : d303417 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301745, d303417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301745, d303417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300539 q = 0) : d302510 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, d302510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31019 q selected
    | true =>
      simp only [d300539, d302510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300540 q = 0) : d302511 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, d302511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300540, d302511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300541 q = 0) : d302512 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, d302512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300541, d302512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301746 q = 0) : d303418 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301746, d303418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301746, d303418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301747 q = 0) : d303419 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301747, d303419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301747, d303419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301766 q = 0) : d303438 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301766, d303438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301766, d303438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro31251 (p : Pattern) (selected : d301772 p = 0) : d303444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301749 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31246 q selected
    | true =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301750 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301751 q = 0) : d303423 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301751, d303423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301751, d303423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301752 q = 0) : d303424 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301752, d303424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301752, d303424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301761 q = 0) : d303433 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301761, d303433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301761, d303433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301767 q = 0) : d303439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301767, d303439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31250 q selected
    | true =>
      simp only [d301767, d303439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301768 q = 0) : d303440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301768, d303440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301768, d303440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301769 q = 0) : d303441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301769, d303441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301769, d303441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301770 q = 0) : d303442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301770, d303442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301770, d303442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301771 q = 0) : d303443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301771, d303443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301771, d303443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301772 q = 0) : d303444 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301772, d303444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301772, d303444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31252 (p : Pattern) (selected : d301779 p = 0) : d303451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301763 q = 0) : d303435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301763, d303435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31247 q selected
    | true =>
      simp only [d301763, d303435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31249 q selected
  have h2 (q : Pattern) (selected : d301764 q = 0) : d303436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301764, d303436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301764, d303436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301765 q = 0) : d303437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301765, d303437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301765, d303437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301773 q = 0) : d303445 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301773, d303445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31249 q selected
    | true =>
      simp only [d301773, d303445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31251 q selected
  have h5 (q : Pattern) (selected : d301774 q = 0) : d303446 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301774, d303446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301774, d303446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301775 q = 0) : d303447 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301775, d303447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301775, d303447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301776 q = 0) : d303448 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301776, d303448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301776, d303448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301777 q = 0) : d303449 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301777, d303449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301777, d303449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301778 q = 0) : d303450 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301778, d303450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301778, d303450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301779 q = 0) : d303451 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301779, d303451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301779, d303451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31253 (p : Pattern) (selected : d301783 p = 0) : d303455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301773 q = 0) : d303445 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301773, d303445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31249 q selected
    | true =>
      simp only [d301773, d303445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31251 q selected
  have h2 (q : Pattern) (selected : d301774 q = 0) : d303446 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301774, d303446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301774, d303446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301775 q = 0) : d303447 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301775, d303447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301775, d303447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301777 q = 0) : d303449 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301777, d303449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301777, d303449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301782 q = 0) : d303454 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301782, d303454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301782, d303454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301783 q = 0) : d303455 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301783, d303455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301783, d303455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31254 (p : Pattern) (selected : d301789 p = 0) : d303461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301780 q = 0) : d303452 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301780, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31252 q selected
    | true =>
      simp only [d301780, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301781 q = 0) : d303453 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301781, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301781, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301784 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31253 q selected
    | true =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301785 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301786 q = 0) : d303458 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301786, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301786, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301787 q = 0) : d303459 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301787, d303459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301787, d303459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301788 q = 0) : d303460 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301788, d303460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301788, d303460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301789 q = 0) : d303461 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301789, d303461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301789, d303461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31255 (p : Pattern) (selected : d301793 p = 0) : d303465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301784 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31253 q selected
    | true =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301785 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301790 q = 0) : d303462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301790, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301790, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301791 q = 0) : d303463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301791, d303463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301791, d303463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301792 q = 0) : d303464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301792, d303464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301792, d303464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301793 q = 0) : d303465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301793, d303465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301793, d303465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31256 (p : Pattern) (selected : d301796 p = 0) : d303528 p = 1 := by
  have h0 (q : Pattern) (selected : d301582 q = 0) : d303396 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301582, d303396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31045 q selected
    | true =>
      simp only [d301582, d303396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31216 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d301583 q = 0) : d303397 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301583, d303397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301583, d303397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300926 q = 0) : d302939 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300926, d302939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31092 q selected
    | true =>
      simp only [d300926, d302939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d300927 q = 0) : d302940 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300927, d302940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300927, d302940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d301584 q = 0) : d303398 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301584, d303398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301584, d303398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301598 q = 0) : d303412 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301598, d303412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301598, d303412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d301599 q = 0) : d303413 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301599, d303413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301599, d303413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301600 q = 0) : d303414 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301600, d303414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301600, d303414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d301796 q = 0) : d303528 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301796, d303528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301796, d303528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h9 p selected
theorem eqIntro31257 (p : Pattern) (selected : d301802 p = 0) : d303534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301614 q = 0) : d303428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301614, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31221 q selected
    | true =>
      simp only [d301614, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301615 q = 0) : d303429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301615, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301615, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301616 q = 0) : d303430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301616, d303430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301616, d303430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301617 q = 0) : d303431 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301617, d303431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301617, d303431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301607 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
    | true =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301608 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301609 q = 0) : d303423 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301609, d303423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301609, d303423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301610 q = 0) : d303424 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301610, d303424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301610, d303424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301618 q = 0) : d303432 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301618, d303432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301618, d303432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301797 q = 0) : d303529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31256 q selected
    | true =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301798 q = 0) : d303530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301799 q = 0) : d303531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301799, d303531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301799, d303531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301800 q = 0) : d303532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301800, d303532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301800, d303532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d301801 q = 0) : d303533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301801, d303533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301801, d303533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301802 q = 0) : d303534 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301802, d303534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301802, d303534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31258 (p : Pattern) (selected : d301803 p = 0) : d303535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301797 q = 0) : d303529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31256 q selected
    | true =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301798 q = 0) : d303530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301799 q = 0) : d303531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301799, d303531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301799, d303531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301800 q = 0) : d303532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301800, d303532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301800, d303532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301801 q = 0) : d303533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301801, d303533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301801, d303533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301803 q = 0) : d303535 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301803, d303535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301803, d303535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31259 (p : Pattern) (selected : d301809 p = 0) : d303541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301621 q = 0) : d303435 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301621, d303435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31220 q selected
    | true =>
      simp only [d301621, d303435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31222 q selected
  have h2 (q : Pattern) (selected : d301622 q = 0) : d303436 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301622, d303436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301622, d303436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301623 q = 0) : d303437 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301623, d303437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301623, d303437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301631 q = 0) : d303445 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301631, d303445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31222 q selected
    | true =>
      simp only [d301631, d303445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31224 q selected
  have h5 (q : Pattern) (selected : d301632 q = 0) : d303446 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301632, d303446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301632, d303446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301633 q = 0) : d303447 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301633, d303447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301633, d303447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301634 q = 0) : d303448 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301634, d303448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301634, d303448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301804 q = 0) : d303536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301804, d303536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31257 q selected
    | true =>
      simp only [d301804, d303536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31258 q selected
  have h9 (q : Pattern) (selected : d301805 q = 0) : d303537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301805, d303537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301805, d303537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301806 q = 0) : d303538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301806, d303538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301806, d303538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301807 q = 0) : d303539 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301807, d303539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301807, d303539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301808 q = 0) : d303540 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301808, d303540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301808, d303540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301809 q = 0) : d303541 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301809, d303541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301809, d303541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro31260 (p : Pattern) (selected : d301815 p = 0) : d303547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301810 q = 0) : d303542 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301810, d303542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31259 q selected
    | true =>
      simp only [d301810, d303542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301811 q = 0) : d303543 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301811, d303543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301811, d303543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301812 q = 0) : d303544 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301812, d303544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301812, d303544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301813 q = 0) : d303545 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301813, d303545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301813, d303545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301814 q = 0) : d303546 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301814, d303546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301814, d303546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301815 q = 0) : d303547 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301815, d303547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301815, d303547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31261 (p : Pattern) (selected : d301821 p = 0) : d303553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301675 q = 0) : d303489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301675, d303489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31233 q selected
    | true =>
      simp only [d301675, d303489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31234 q selected
  have h2 (q : Pattern) (selected : d301676 q = 0) : d303490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301676, d303490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301676, d303490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301677 q = 0) : d303491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301677, d303491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301677, d303491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301678 q = 0) : d303492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301678, d303492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301678, d303492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301685 q = 0) : d303499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301685, d303499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31235 q selected
    | true =>
      simp only [d301685, d303499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31236 q selected
  have h6 (q : Pattern) (selected : d301686 q = 0) : d303500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301686, d303500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301686, d303500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301687 q = 0) : d303501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301687, d303501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301687, d303501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301712 q = 0) : d303526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301712, d303526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31241 q selected
    | true =>
      simp only [d301712, d303526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31227 q selected
  have h9 (q : Pattern) (selected : d301794 q = 0) : d303466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301794, d303466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31254 q selected
    | true =>
      simp only [d301794, d303466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31255 q selected
  have h10 (q : Pattern) (selected : d301795 q = 0) : d303527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301795, d303527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301795, d303527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301816 q = 0) : d303548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301816, d303548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31260 q selected
    | true =>
      simp only [d301816, d303548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301817 q = 0) : d303549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301817, d303549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301817, d303549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301818 q = 0) : d303550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301818, d303550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301818, d303550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301819 q = 0) : d303551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301819, d303551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301819, d303551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d301820 q = 0) : d303552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301820, d303552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301820, d303552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301821 q = 0) : d303553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301821, d303553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301821, d303553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro31262 (p : Pattern) (selected : d301822 p = 0) : d303554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301638 q = 0) : d303452 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301638, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31225 q selected
    | true =>
      simp only [d301638, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301639 q = 0) : d303453 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301639, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301639, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301642 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31226 q selected
    | true =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301643 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301644 q = 0) : d303458 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301644, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301644, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301645 q = 0) : d303459 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301645, d303459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301645, d303459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301671 q = 0) : d303485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301671, d303485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301671, d303485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301822 q = 0) : d303554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301822, d303554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301822, d303554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31263 (p : Pattern) (selected : d301823 p = 0) : d303555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301642 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31226 q selected
    | true =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301643 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301648 q = 0) : d303462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301648, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301648, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301649 q = 0) : d303463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301649, d303463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301649, d303463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301673 q = 0) : d303487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301673, d303487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301673, d303487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301823 q = 0) : d303555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301823, d303555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301823, d303555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31264 (p : Pattern) (selected : d301828 p = 0) : d303560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301638 q = 0) : d303452 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301638, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31225 q selected
    | true =>
      simp only [d301638, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301639 q = 0) : d303453 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301639, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301639, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301642 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31226 q selected
    | true =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301643 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301644 q = 0) : d303458 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301644, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301644, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301679 q = 0) : d303493 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301679, d303493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301679, d303493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301680 q = 0) : d303494 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301680, d303494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301680, d303494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301828 q = 0) : d303560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301828, d303560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301828, d303560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31265 (p : Pattern) (selected : d301829 p = 0) : d303561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301642 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31226 q selected
    | true =>
      simp only [d301642, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301643 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301643, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301648 q = 0) : d303462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301648, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301648, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301682 q = 0) : d303496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301682, d303496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301682, d303496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301683 q = 0) : d303497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301683, d303497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301683, d303497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301829 q = 0) : d303561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301829, d303561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301829, d303561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31266 (p : Pattern) (selected : d301833 p = 0) : d303565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301706 q = 0) : d303520 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301706, d303520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31240 q selected
    | true =>
      simp only [d301706, d303520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301707 q = 0) : d303521 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301707, d303521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301707, d303521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301638 q = 0) : d303452 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301638, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31225 q selected
    | true =>
      simp only [d301638, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301639 q = 0) : d303453 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301639, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301639, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301708 q = 0) : d303522 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301708, d303522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301708, d303522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301709 q = 0) : d303523 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301709, d303523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301709, d303523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301710 q = 0) : d303524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301710, d303524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301710, d303524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301833 q = 0) : d303565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301833, d303565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301833, d303565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31267 (p : Pattern) (selected : d301835 p = 0) : d303474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301780 q = 0) : d303452 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301780, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31252 q selected
    | true =>
      simp only [d301780, d303452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301781 q = 0) : d303453 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301781, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301781, d303453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301784 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31253 q selected
    | true =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301785 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301786 q = 0) : d303458 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301786, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301786, d303458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301787 q = 0) : d303459 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301787, d303459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301787, d303459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301788 q = 0) : d303460 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301788, d303460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301788, d303460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301835 q = 0) : d303474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301835, d303474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301835, d303474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31268 (p : Pattern) (selected : d301836 p = 0) : d303475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301784 q = 0) : d303456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31253 q selected
    | true =>
      simp only [d301784, d303456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301785 q = 0) : d303457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, d303457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301790 q = 0) : d303462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301790, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301790, d303462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301791 q = 0) : d303463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301791, d303463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301791, d303463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301792 q = 0) : d303464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301792, d303464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301792, d303464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301836 q = 0) : d303475 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301836, d303475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301836, d303475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31269 (p : Pattern) (selected : d301839 p = 0) : d303568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301810 q = 0) : d303542 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301810, d303542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31259 q selected
    | true =>
      simp only [d301810, d303542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301811 q = 0) : d303543 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301811, d303543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301811, d303543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301812 q = 0) : d303544 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301812, d303544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301812, d303544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301813 q = 0) : d303545 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301813, d303545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301813, d303545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301814 q = 0) : d303546 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301814, d303546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301814, d303546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301839 q = 0) : d303568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301839, d303568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301839, d303568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31270 (p : Pattern) (selected : d301845 p = 0) : d303574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301675 q = 0) : d303489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301675, d303489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31233 q selected
    | true =>
      simp only [d301675, d303489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31234 q selected
  have h2 (q : Pattern) (selected : d301676 q = 0) : d303490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301676, d303490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301676, d303490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301677 q = 0) : d303491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301677, d303491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301677, d303491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301678 q = 0) : d303492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301678, d303492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301678, d303492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301685 q = 0) : d303499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301685, d303499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31235 q selected
    | true =>
      simp only [d301685, d303499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31236 q selected
  have h6 (q : Pattern) (selected : d301686 q = 0) : d303500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301686, d303500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301686, d303500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301687 q = 0) : d303501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301687, d303501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301687, d303501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301712 q = 0) : d303526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301712, d303526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31241 q selected
    | true =>
      simp only [d301712, d303526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31227 q selected
  have h9 (q : Pattern) (selected : d301794 q = 0) : d303466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301794, d303466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31254 q selected
    | true =>
      simp only [d301794, d303466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31255 q selected
  have h10 (q : Pattern) (selected : d301795 q = 0) : d303527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301795, d303527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301795, d303527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301816 q = 0) : d303548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301816, d303548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31260 q selected
    | true =>
      simp only [d301816, d303548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301817 q = 0) : d303549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301817, d303549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301817, d303549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301818 q = 0) : d303550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301818, d303550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301818, d303550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301819 q = 0) : d303551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301819, d303551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301819, d303551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d301820 q = 0) : d303552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301820, d303552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301820, d303552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301824 q = 0) : d303556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301824, d303556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31262 q selected
    | true =>
      simp only [d301824, d303556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31263 q selected
  have h17 (q : Pattern) (selected : d301825 q = 0) : d303557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301825, d303557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301825, d303557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d301826 q = 0) : d303558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301826, d303558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d301826, d303558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d301827 q = 0) : d303559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301827, d303559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301827, d303559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d301830 q = 0) : d303562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301830, d303562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31264 q selected
    | true =>
      simp only [d301830, d303562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31265 q selected
  have h21 (q : Pattern) (selected : d301831 q = 0) : d303563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301831, d303563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301831, d303563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d301832 q = 0) : d303564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301832, d303564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d301832, d303564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d301834 q = 0) : d303566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301834, d303566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31266 q selected
    | true =>
      simp only [d301834, d303566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31230 q selected
  have h24 (q : Pattern) (selected : d301837 q = 0) : d303476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301837, d303476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31267 q selected
    | true =>
      simp only [d301837, d303476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31268 q selected
  have h25 (q : Pattern) (selected : d301838 q = 0) : d303567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301838, d303567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d301838, d303567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d301840 q = 0) : d303569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301840, d303569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31269 q selected
    | true =>
      simp only [d301840, d303569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d301841 q = 0) : d303570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301841, d303570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d301841, d303570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d301842 q = 0) : d303571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301842, d303571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d301842, d303571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d301843 q = 0) : d303572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301843, d303572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d301843, d303572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d301844 q = 0) : d303573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301844, d303573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d301844, d303573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d301845 q = 0) : d303574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301845, d303574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301845, d303574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro31271 (p : Pattern) (selected : d301852 p = 0) : d303581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301652 q = 0) : d303466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301652, d303466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31227 q selected
    | true =>
      simp only [d301652, d303466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31228 q selected
  have h2 (q : Pattern) (selected : d301653 q = 0) : d303467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301653, d303467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301653, d303467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301654 q = 0) : d303468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301654, d303468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301654, d303468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301655 q = 0) : d303469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301655, d303469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301655, d303469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301656 q = 0) : d303470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301656, d303470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301656, d303470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301847 q = 0) : d303576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301847, d303576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31228 q selected
    | true =>
      simp only [d301847, d303576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301848 q = 0) : d303577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301848, d303577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301848, d303577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301849 q = 0) : d303578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301849, d303578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301849, d303578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301850 q = 0) : d303579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301850, d303579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301850, d303579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301851 q = 0) : d303580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301851, d303580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301851, d303580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301852 q = 0) : d303581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301852, d303581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301852, d303581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31272 (p : Pattern) (selected : d301858 p = 0) : d303587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301847 q = 0) : d303576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301847, d303576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31228 q selected
    | true =>
      simp only [d301847, d303576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301848 q = 0) : d303577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301848, d303577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301848, d303577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301849 q = 0) : d303578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301849, d303578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301849, d303578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301850 q = 0) : d303579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301850, d303579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301850, d303579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301851 q = 0) : d303580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301851, d303580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301851, d303580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301853 q = 0) : d303582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301853, d303582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31231 q selected
    | true =>
      simp only [d301853, d303582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301854 q = 0) : d303583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301854, d303583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301854, d303583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301855 q = 0) : d303584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301855, d303584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301855, d303584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301856 q = 0) : d303585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301856, d303585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301856, d303585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301857 q = 0) : d303586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301857, d303586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301857, d303586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301858 q = 0) : d303587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301858, d303587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301858, d303587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31273 (p : Pattern) (selected : d301865 p = 0) : d303594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301834 q = 0) : d303566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301834, d303566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31266 q selected
    | true =>
      simp only [d301834, d303566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31230 q selected
  have h2 (q : Pattern) (selected : d301837 q = 0) : d303476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301837, d303476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31267 q selected
    | true =>
      simp only [d301837, d303476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31268 q selected
  have h3 (q : Pattern) (selected : d301838 q = 0) : d303567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301838, d303567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301838, d303567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301840 q = 0) : d303569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301840, d303569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31269 q selected
    | true =>
      simp only [d301840, d303569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301841 q = 0) : d303570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301841, d303570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301841, d303570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301842 q = 0) : d303571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301842, d303571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301842, d303571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301863 q = 0) : d303592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301863, d303592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301863, d303592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301864 q = 0) : d303593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301864, d303593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301864, d303593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301865 q = 0) : d303594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301865, d303594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301865, d303594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro31274 (p : Pattern) (selected : d301867 p = 0) : d303596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301853 q = 0) : d303582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301853, d303582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31231 q selected
    | true =>
      simp only [d301853, d303582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301854 q = 0) : d303583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301854, d303583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301854, d303583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301855 q = 0) : d303584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301855, d303584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301855, d303584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301856 q = 0) : d303585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301856, d303585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301856, d303585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301857 q = 0) : d303586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301857, d303586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301857, d303586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301867 q = 0) : d303596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301867, d303596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301867, d303596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31275 (p : Pattern) (selected : d301883 p = 0) : d303612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301873 q = 0) : d303602 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301873, d303602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301873, d303602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31237 q selected
  have h2 (q : Pattern) (selected : d301689 q = 0) : d303503 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301689, d303503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31237 q selected
    | true =>
      simp only [d301689, d303503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301874 q = 0) : d303603 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301874, d303603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301874, d303603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301690 q = 0) : d303504 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301690, d303504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301690, d303504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301875 q = 0) : d303604 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301875, d303604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301875, d303604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301876 q = 0) : d303605 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301876, d303605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301876, d303605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301877 q = 0) : d303606 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301877, d303606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301877, d303606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301878 q = 0) : d303607 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301878, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301878, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31218 q selected
  have h9 (q : Pattern) (selected : d301594 q = 0) : d303408 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301594, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31218 q selected
    | true =>
      simp only [d301594, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301879 q = 0) : d303608 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301879, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301879, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301595 q = 0) : d303409 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301595, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301595, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301880 q = 0) : d303609 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301880, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301880, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301881 q = 0) : d303610 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301881, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301881, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d301882 q = 0) : d303611 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301882, d303611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301882, d303611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d301883 q = 0) : d303612 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301883, d303612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301883, d303612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31276 (p : Pattern) (selected : d301894 p = 0) : d303623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301434 q = 0) : d303295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301434, d303295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301434, d303295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31158 q selected
  have h2 (q : Pattern) (selected : d301269 q = 0) : d303200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301269, d303200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31158 q selected
    | true =>
      simp only [d301269, d303200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301435 q = 0) : d303296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301435, d303296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301435, d303296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301270 q = 0) : d303201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301270, d303201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301270, d303201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301436 q = 0) : d303297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301436, d303297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301436, d303297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301437 q = 0) : d303298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301437, d303298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301437, d303298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301884 q = 0) : d303613 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301884, d303613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301884, d303613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31217 q selected
  have h8 (q : Pattern) (selected : d301588 q = 0) : d303402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301588, d303402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31217 q selected
    | true =>
      simp only [d301588, d303402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301885 q = 0) : d303614 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301885, d303614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301885, d303614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301589 q = 0) : d303403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301589, d303403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301589, d303403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301886 q = 0) : d303615 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301886, d303615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301886, d303615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301887 q = 0) : d303616 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301887, d303616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301887, d303616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301888 q = 0) : d303617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301888, d303617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301888, d303617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301878 q = 0) : d303607 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301878, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301878, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31218 q selected
  have h15 (q : Pattern) (selected : d301594 q = 0) : d303408 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301594, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31218 q selected
    | true =>
      simp only [d301594, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301879 q = 0) : d303608 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301879, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301879, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301595 q = 0) : d303409 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301595, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301595, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d301880 q = 0) : d303609 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301880, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301880, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d301881 q = 0) : d303610 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301881, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d301881, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d301889 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
  have h21 (q : Pattern) (selected : d301607 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
    | true =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d301890 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d301608 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d301891 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d301892 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d301893 q = 0) : d303622 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301893, d303622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d301893, d303622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d301894 q = 0) : d303623 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301894, d303623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301894, d303623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro31277 (p : Pattern) (selected : d301899 p = 0) : d303628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301878 q = 0) : d303607 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301878, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301878, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31218 q selected
  have h2 (q : Pattern) (selected : d301594 q = 0) : d303408 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301594, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31218 q selected
    | true =>
      simp only [d301594, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301879 q = 0) : d303608 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301879, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301879, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301595 q = 0) : d303409 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301595, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301595, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301880 q = 0) : d303609 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301880, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301880, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301881 q = 0) : d303610 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301881, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301881, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301889 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
  have h8 (q : Pattern) (selected : d301607 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
    | true =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301890 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301608 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301891 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301892 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301893 q = 0) : d303622 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301893, d303622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301893, d303622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301898 q = 0) : d303627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301898, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301898, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301899 q = 0) : d303628 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301899, d303628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301899, d303628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31278 (p : Pattern) (selected : d301909 p = 0) : d303638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301904 q = 0) : d303633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301904, d303633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301904, d303633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31221 q selected
  have h2 (q : Pattern) (selected : d301614 q = 0) : d303428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301614, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31221 q selected
    | true =>
      simp only [d301614, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301905 q = 0) : d303634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301905, d303634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301905, d303634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301615 q = 0) : d303429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301615, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301615, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301906 q = 0) : d303635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301906, d303635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301906, d303635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301907 q = 0) : d303636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301907, d303636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301907, d303636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301889 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
  have h8 (q : Pattern) (selected : d301607 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
    | true =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301890 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301608 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301891 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301892 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301908 q = 0) : d303637 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301908, d303637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301908, d303637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301898 q = 0) : d303627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301898, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301898, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301909 q = 0) : d303638 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301909, d303638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301909, d303638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31279 (p : Pattern) (selected : d301918 p = 0) : d303647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301889 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
  have h2 (q : Pattern) (selected : d301607 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
    | true =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301890 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301608 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301891 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301892 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301898 q = 0) : d303627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301898, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301898, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301913 q = 0) : d303642 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301913, d303642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301913, d303642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31223 q selected
  have h9 (q : Pattern) (selected : d301625 q = 0) : d303439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301625, d303439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31223 q selected
    | true =>
      simp only [d301625, d303439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301914 q = 0) : d303643 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301914, d303643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301914, d303643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301626 q = 0) : d303440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301626, d303440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301626, d303440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301915 q = 0) : d303644 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301915, d303644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301915, d303644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301916 q = 0) : d303645 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301916, d303645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301916, d303645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d301917 q = 0) : d303646 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301917, d303646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301917, d303646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301918 q = 0) : d303647 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301918, d303647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301918, d303647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31280 (p : Pattern) (selected : d301924 p = 0) : d303653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301895 q = 0) : d303624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301895, d303624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31275 q selected
    | true =>
      simp only [d301895, d303624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31276 q selected
  have h2 (q : Pattern) (selected : d301896 q = 0) : d303625 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301896, d303625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301896, d303625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301897 q = 0) : d303626 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301897, d303626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301897, d303626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301900 q = 0) : d303629 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301900, d303629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31276 q selected
    | true =>
      simp only [d301900, d303629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31277 q selected
  have h5 (q : Pattern) (selected : d301901 q = 0) : d303630 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301901, d303630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301901, d303630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301902 q = 0) : d303631 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301902, d303631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301902, d303631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301903 q = 0) : d303632 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301903, d303632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301903, d303632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301910 q = 0) : d303639 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301910, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31276 q selected
    | true =>
      simp only [d301910, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31278 q selected
  have h9 (q : Pattern) (selected : d301911 q = 0) : d303640 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301911, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301911, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301912 q = 0) : d303641 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301912, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301912, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301919 q = 0) : d303648 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31278 q selected
    | true =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31279 q selected
  have h12 (q : Pattern) (selected : d301920 q = 0) : d303649 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301921 q = 0) : d303650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301922 q = 0) : d303651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301922, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301922, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d301923 q = 0) : d303652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301923, d303652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301923, d303652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301924 q = 0) : d303653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301924, d303653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301924, d303653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro31281 (p : Pattern) (selected : d301929 p = 0) : d303658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301910 q = 0) : d303639 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301910, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31276 q selected
    | true =>
      simp only [d301910, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31278 q selected
  have h2 (q : Pattern) (selected : d301911 q = 0) : d303640 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301911, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301911, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301912 q = 0) : d303641 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301912, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301912, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301919 q = 0) : d303648 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31278 q selected
    | true =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31279 q selected
  have h5 (q : Pattern) (selected : d301920 q = 0) : d303649 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301921 q = 0) : d303650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301922 q = 0) : d303651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301922, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301922, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301927 q = 0) : d303656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301927, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301927, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301928 q = 0) : d303657 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301928, d303657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301928, d303657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301929 q = 0) : d303658 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301929, d303658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301929, d303658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31282 (p : Pattern) (selected : d301935 p = 0) : d303664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301925 q = 0) : d303654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301925, d303654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31280 q selected
    | true =>
      simp only [d301925, d303654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301926 q = 0) : d303655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301926, d303655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301926, d303655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301930 q = 0) : d303659 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301930, d303659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31281 q selected
    | true =>
      simp only [d301930, d303659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301931 q = 0) : d303660 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301931, d303660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301931, d303660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301932 q = 0) : d303661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301932, d303661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301932, d303661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301933 q = 0) : d303662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301933, d303662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301933, d303662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301934 q = 0) : d303663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301934, d303663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301934, d303663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301935 q = 0) : d303664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301935, d303664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301935, d303664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31283 (p : Pattern) (selected : d301937 p = 0) : d303666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301919 q = 0) : d303648 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31278 q selected
    | true =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31279 q selected
  have h2 (q : Pattern) (selected : d301920 q = 0) : d303649 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301921 q = 0) : d303650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301927 q = 0) : d303656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301927, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301927, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301936 q = 0) : d303665 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301936, d303665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301936, d303665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301937 q = 0) : d303666 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301937, d303666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301937, d303666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31284 (p : Pattern) (selected : d301943 p = 0) : d303672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301930 q = 0) : d303659 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301930, d303659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31281 q selected
    | true =>
      simp only [d301930, d303659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301931 q = 0) : d303660 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301931, d303660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301931, d303660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301938 q = 0) : d303667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301938, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31283 q selected
    | true =>
      simp only [d301938, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301939 q = 0) : d303668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301939, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301939, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301940 q = 0) : d303669 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301940, d303669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301940, d303669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301941 q = 0) : d303670 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301941, d303670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301941, d303670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301942 q = 0) : d303671 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301942, d303671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301942, d303671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301943 q = 0) : d303672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301943, d303672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301943, d303672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31285 (p : Pattern) (selected : d301963 p = 0) : d303623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301945 q = 0) : d303295 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301945, d303295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301945, d303295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31242 q selected
  have h2 (q : Pattern) (selected : d301717 q = 0) : d303200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301717, d303200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31242 q selected
    | true =>
      simp only [d301717, d303200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301946 q = 0) : d303296 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301946, d303296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301946, d303296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301718 q = 0) : d303201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301718, d303201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301718, d303201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301947 q = 0) : d303297 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301947, d303297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301947, d303297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301948 q = 0) : d303298 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301948, d303298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301948, d303298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301949 q = 0) : d303613 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301949, d303613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301949, d303613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31244 q selected
  have h8 (q : Pattern) (selected : d301728 q = 0) : d303402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301728, d303402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31244 q selected
    | true =>
      simp only [d301728, d303402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301950 q = 0) : d303614 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301950, d303614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301950, d303614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301729 q = 0) : d303403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301729, d303403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301729, d303403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301951 q = 0) : d303615 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301951, d303615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301951, d303615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301952 q = 0) : d303616 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301952, d303616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301952, d303616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301953 q = 0) : d303617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301953, d303617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301953, d303617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301954 q = 0) : d303607 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301954, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301954, d303607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31245 q selected
  have h15 (q : Pattern) (selected : d301736 q = 0) : d303408 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301736, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31245 q selected
    | true =>
      simp only [d301736, d303408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301955 q = 0) : d303608 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301955, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301955, d303608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301737 q = 0) : d303409 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301737, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301737, d303409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d301956 q = 0) : d303609 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301956, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301956, d303609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d301957 q = 0) : d303610 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301957, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d301957, d303610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d301958 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301958, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301958, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31246 q selected
  have h21 (q : Pattern) (selected : d301749 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31246 q selected
    | true =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d301959 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301959, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d301959, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d301750 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d301960 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301960, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d301960, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d301961 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301961, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d301961, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d301962 q = 0) : d303622 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301962, d303622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d301962, d303622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d301963 q = 0) : d303623 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301963, d303623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301963, d303623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro31286 (p : Pattern) (selected : d301970 p = 0) : d303638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301964 q = 0) : d303633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301964, d303633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301964, d303633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31248 q selected
  have h2 (q : Pattern) (selected : d301756 q = 0) : d303428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301756, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31248 q selected
    | true =>
      simp only [d301756, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301965 q = 0) : d303634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301965, d303634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301965, d303634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301757 q = 0) : d303429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301757, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301757, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301966 q = 0) : d303635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301966, d303635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301966, d303635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301967 q = 0) : d303636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301967, d303636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301967, d303636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301958 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301958, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301958, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31246 q selected
  have h8 (q : Pattern) (selected : d301749 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31246 q selected
    | true =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301959 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301959, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301959, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301750 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301960 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301960, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301960, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301961 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301961, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301961, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301968 q = 0) : d303637 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301968, d303637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301968, d303637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301969 q = 0) : d303627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301969, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301969, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301970 q = 0) : d303638 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301970, d303638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301970, d303638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31287 (p : Pattern) (selected : d301979 p = 0) : d303647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301958 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301958, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301958, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31246 q selected
  have h2 (q : Pattern) (selected : d301749 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31246 q selected
    | true =>
      simp only [d301749, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301959 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301959, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301959, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301750 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301750, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301960 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301960, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301960, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301961 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301961, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301961, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301969 q = 0) : d303627 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301969, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301969, d303627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301974 q = 0) : d303642 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301974, d303642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301974, d303642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31250 q selected
  have h9 (q : Pattern) (selected : d301767 q = 0) : d303439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301767, d303439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31250 q selected
    | true =>
      simp only [d301767, d303439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301975 q = 0) : d303643 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301975, d303643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301975, d303643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301768 q = 0) : d303440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301768, d303440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301768, d303440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301976 q = 0) : d303644 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301976, d303644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301976, d303644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301977 q = 0) : d303645 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301977, d303645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301977, d303645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d301978 q = 0) : d303646 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301978, d303646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301978, d303646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301979 q = 0) : d303647 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301979, d303647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301979, d303647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31288 (p : Pattern) (selected : d301986 p = 0) : d303658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301971 q = 0) : d303639 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301971, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31285 q selected
    | true =>
      simp only [d301971, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31286 q selected
  have h2 (q : Pattern) (selected : d301972 q = 0) : d303640 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301972, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301972, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301973 q = 0) : d303641 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301973, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301973, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301980 q = 0) : d303648 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301980, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31286 q selected
    | true =>
      simp only [d301980, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31287 q selected
  have h5 (q : Pattern) (selected : d301981 q = 0) : d303649 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301981, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301981, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301982 q = 0) : d303650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301982, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301982, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301983 q = 0) : d303651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301983, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301983, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301984 q = 0) : d303656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301984, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301984, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301985 q = 0) : d303657 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301985, d303657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301985, d303657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301986 q = 0) : d303658 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301986, d303658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301986, d303658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31289 (p : Pattern) (selected : d301990 p = 0) : d303666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301980 q = 0) : d303648 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301980, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31286 q selected
    | true =>
      simp only [d301980, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31287 q selected
  have h2 (q : Pattern) (selected : d301981 q = 0) : d303649 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301981, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301981, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301982 q = 0) : d303650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301982, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301982, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301984 q = 0) : d303656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301984, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301984, d303656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301989 q = 0) : d303665 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301989, d303665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301989, d303665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301990 q = 0) : d303666 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301990, d303666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301990, d303666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31290 (p : Pattern) (selected : d301996 p = 0) : d303672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301987 q = 0) : d303659 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301987, d303659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31288 q selected
    | true =>
      simp only [d301987, d303659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301988 q = 0) : d303660 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301988, d303660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301988, d303660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301991 q = 0) : d303667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301991, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31289 q selected
    | true =>
      simp only [d301991, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301992 q = 0) : d303668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301992, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301992, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301993 q = 0) : d303669 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301993, d303669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301993, d303669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301994 q = 0) : d303670 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301994, d303670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301994, d303670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301995 q = 0) : d303671 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301995, d303671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301995, d303671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301996 q = 0) : d303672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301996, d303672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301996, d303672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31291 (p : Pattern) (selected : d302000 p = 0) : d303677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301991 q = 0) : d303667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301991, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31289 q selected
    | true =>
      simp only [d301991, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301992 q = 0) : d303668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301992, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301992, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301997 q = 0) : d303674 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301997, d303674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301997, d303674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301998 q = 0) : d303675 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301998, d303675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301998, d303675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301999 q = 0) : d303676 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301999, d303676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301999, d303676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302000 q = 0) : d303677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302000, d303677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302000, d303677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31292 (p : Pattern) (selected : d302008 p = 0) : d303685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301904 q = 0) : d303633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301904, d303633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301904, d303633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31221 q selected
  have h2 (q : Pattern) (selected : d301614 q = 0) : d303428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301614, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31221 q selected
    | true =>
      simp only [d301614, d303428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301905 q = 0) : d303634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301905, d303634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301905, d303634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301615 q = 0) : d303429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301615, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301615, d303429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301906 q = 0) : d303635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301906, d303635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301906, d303635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301907 q = 0) : d303636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301907, d303636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301907, d303636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301889 q = 0) : d303618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301889, d303618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
  have h8 (q : Pattern) (selected : d301607 q = 0) : d303421 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31219 q selected
    | true =>
      simp only [d301607, d303421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301890 q = 0) : d303619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301890, d303619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301608 q = 0) : d303422 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301608, d303422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301891 q = 0) : d303620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301891, d303620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301892 q = 0) : d303621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301892, d303621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301908 q = 0) : d303637 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301908, d303637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301908, d303637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302003 q = 0) : d303680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302003, d303680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302003, d303680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31256 q selected
  have h15 (q : Pattern) (selected : d301797 q = 0) : d303529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31256 q selected
    | true =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d302004 q = 0) : d303681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302004, d303681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d302004, d303681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301798 q = 0) : d303530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d302005 q = 0) : d303682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302005, d303682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d302005, d303682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d302006 q = 0) : d303683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302006, d303683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d302006, d303683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d302007 q = 0) : d303684 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302007, d303684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d302007, d303684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d302008 q = 0) : d303685 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302008, d303685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302008, d303685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro31293 (p : Pattern) (selected : d302009 p = 0) : d303686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302003 q = 0) : d303680 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302003, d303680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302003, d303680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31256 q selected
  have h2 (q : Pattern) (selected : d301797 q = 0) : d303529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31256 q selected
    | true =>
      simp only [d301797, d303529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302004 q = 0) : d303681 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302004, d303681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302004, d303681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301798 q = 0) : d303530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301798, d303530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302005 q = 0) : d303682 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302005, d303682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302005, d303682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302006 q = 0) : d303683 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302006, d303683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302006, d303683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302007 q = 0) : d303684 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302007, d303684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302007, d303684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302009 q = 0) : d303686 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302009, d303686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302009, d303686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31294 (p : Pattern) (selected : d302015 p = 0) : d303692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301910 q = 0) : d303639 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301910, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31276 q selected
    | true =>
      simp only [d301910, d303639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31278 q selected
  have h2 (q : Pattern) (selected : d301911 q = 0) : d303640 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301911, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301911, d303640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301912 q = 0) : d303641 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301912, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301912, d303641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301919 q = 0) : d303648 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31278 q selected
    | true =>
      simp only [d301919, d303648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31279 q selected
  have h5 (q : Pattern) (selected : d301920 q = 0) : d303649 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301920, d303649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301921 q = 0) : d303650 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301921, d303650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301922 q = 0) : d303651 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301922, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301922, d303651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302010 q = 0) : d303687 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302010, d303687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31292 q selected
    | true =>
      simp only [d302010, d303687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31293 q selected
  have h9 (q : Pattern) (selected : d302011 q = 0) : d303688 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302011, d303688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302011, d303688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302012 q = 0) : d303689 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302012, d303689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302012, d303689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302013 q = 0) : d303690 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302013, d303690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302013, d303690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302014 q = 0) : d303691 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302014, d303691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302014, d303691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302015 q = 0) : d303692 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302015, d303692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302015, d303692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro31295 (p : Pattern) (selected : d302021 p = 0) : d303698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302016 q = 0) : d303693 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302016, d303693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31294 q selected
    | true =>
      simp only [d302016, d303693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302017 q = 0) : d303694 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302017, d303694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302017, d303694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302018 q = 0) : d303695 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302018, d303695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302018, d303695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302019 q = 0) : d303696 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302019, d303696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302019, d303696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302020 q = 0) : d303697 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302020, d303697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302020, d303697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302021 q = 0) : d303698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302021, d303698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302021, d303698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31296 (p : Pattern) (selected : d302027 p = 0) : d303704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301944 q = 0) : d303673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301944, d303673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31282 q selected
    | true =>
      simp only [d301944, d303673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31284 q selected
  have h2 (q : Pattern) (selected : d302001 q = 0) : d303678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302001, d303678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31290 q selected
    | true =>
      simp only [d302001, d303678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31291 q selected
  have h3 (q : Pattern) (selected : d302002 q = 0) : d303679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302002, d303679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302002, d303679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302022 q = 0) : d303699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302022, d303699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31295 q selected
    | true =>
      simp only [d302022, d303699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302023 q = 0) : d303700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302023, d303700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302023, d303700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302024 q = 0) : d303701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302024, d303701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302024, d303701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302025 q = 0) : d303702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302025, d303702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302025, d303702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302026 q = 0) : d303703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302026, d303703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302026, d303703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302027 q = 0) : d303704 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302027, d303704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302027, d303704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro31297 (p : Pattern) (selected : d302032 p = 0) : d303677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301938 q = 0) : d303667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301938, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31283 q selected
    | true =>
      simp only [d301938, d303667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301939 q = 0) : d303668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301939, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301939, d303668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302029 q = 0) : d303674 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302029, d303674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302029, d303674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302030 q = 0) : d303675 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302030, d303675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302030, d303675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302031 q = 0) : d303676 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302031, d303676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302031, d303676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302032 q = 0) : d303677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302032, d303677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302032, d303677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31298 (p : Pattern) (selected : d302038 p = 0) : d303711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302033 q = 0) : d303706 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302033, d303706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31297 q selected
    | true =>
      simp only [d302033, d303706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302034 q = 0) : d303707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302034, d303707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302034, d303707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302035 q = 0) : d303708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302035, d303708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302035, d303708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302036 q = 0) : d303709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302036, d303709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302036, d303709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302037 q = 0) : d303710 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302037, d303710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302037, d303710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302038 q = 0) : d303711 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302038, d303711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302038, d303711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31299 (p : Pattern) (selected : d302044 p = 0) : d303717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d301658 q = 0) : d303472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301658, d303472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301658, d303472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31229 q selected
  have h2 (q : Pattern) (selected : d301659 q = 0) : d303473 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301659, d303473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301659, d303473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301668 q = 0) : d303482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301668, d303482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31229 q selected
    | true =>
      simp only [d301668, d303482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31232 q selected
  have h4 (q : Pattern) (selected : d301669 q = 0) : d303483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301669, d303483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301669, d303483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301670 q = 0) : d303484 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301670, d303484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301670, d303484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301846 q = 0) : d303575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301846, d303575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31261 q selected
    | true =>
      simp only [d301846, d303575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31270 q selected
  have h7 (q : Pattern) (selected : d301859 q = 0) : d303588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301859, d303588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31271 q selected
    | true =>
      simp only [d301859, d303588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31272 q selected
  have h8 (q : Pattern) (selected : d301860 q = 0) : d303589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301860, d303589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301860, d303589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301861 q = 0) : d303590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301861, d303590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301861, d303590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301862 q = 0) : d303591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301862, d303591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301862, d303591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301866 q = 0) : d303595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301866, d303595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301866, d303595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31273 q selected
  have h12 (q : Pattern) (selected : d301868 q = 0) : d303597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301868, d303597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301868, d303597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31274 q selected
  have h13 (q : Pattern) (selected : d301869 q = 0) : d303598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301869, d303598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301869, d303598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301870 q = 0) : d303599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301870, d303599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301870, d303599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301871 q = 0) : d303600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301871, d303600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301871, d303600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301872 q = 0) : d303601 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d301872, d303601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301872, d303601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d302028 q = 0) : d303705 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302028, d303705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302028, d303705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31296 q selected
  have h18 (q : Pattern) (selected : d302039 q = 0) : d303712 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302039, d303712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302039, d303712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31298 q selected
  have h19 (q : Pattern) (selected : d302040 q = 0) : d303713 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302040, d303713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d302040, d303713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d302041 q = 0) : d303714 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302041, d303714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d302041, d303714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d302042 q = 0) : d303715 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302042, d303715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d302042, d303715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d302043 q = 0) : d303716 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302043, d303716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d302043, d303716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d302044 q = 0) : d303717 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d302044, d303717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d302044, d303717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro31300 (p : Pattern) (selected : d302050 p = 0) : d303723 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302045 q = 0) : d303718 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d302045, d303718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302045, d303718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31299 q selected
  have h2 (q : Pattern) (selected : d302046 q = 0) : d303719 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d302046, d303719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302046, d303719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302047 q = 0) : d303720 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d302047, d303720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302047, d303720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302048 q = 0) : d303721 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d302048, d303721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302048, d303721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302049 q = 0) : d303722 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d302049, d303722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302049, d303722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302050 q = 0) : d303723 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d302050, d303723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302050, d303723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31301 (p : Pattern) (selected : d302055 p = 0) : d303728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1523 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1523, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302055 q = 0) : d303728 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d302055, d303728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302055, d303728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro31302 (p : Pattern) (selected : d302058 p = 0) : d303731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d307 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1997 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302058 q = 0) : d303731 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d302058, d303731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302058, d303731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro31303 (p : Pattern) (selected : d302064 p = 0) : d303737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302056 q = 0) : d303729 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302056, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302056, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31301 q selected
  have h2 (q : Pattern) (selected : d302057 q = 0) : d303730 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302057, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302057, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302059 q = 0) : d303732 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302059, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31302 q selected
    | true =>
      simp only [d302059, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302060 q = 0) : d303733 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302060, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302060, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302061 q = 0) : d303734 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302061, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302061, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302062 q = 0) : d303735 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302062, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302062, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302063 q = 0) : d303736 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302063, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302063, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302064 q = 0) : d303737 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d302064, d303737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302064, d303737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31304 (p : Pattern) (selected : d302070 p = 0) : d303743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2016 q = 0) : d53295 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2016, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302070 q = 0) : d303743 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d302070, d303743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302070, d303743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31305 (p : Pattern) (selected : d302079 p = 0) : d303752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302056 q = 0) : d303729 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302056, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302056, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31301 q selected
  have h2 (q : Pattern) (selected : d302057 q = 0) : d303730 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302057, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302057, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302059 q = 0) : d303732 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302059, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31302 q selected
    | true =>
      simp only [d302059, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302060 q = 0) : d303733 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302060, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302060, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302061 q = 0) : d303734 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302061, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302061, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302062 q = 0) : d303735 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302062, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302062, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302063 q = 0) : d303736 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302063, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302063, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302071 q = 0) : d303744 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302071, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302071, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31304 q selected
  have h9 (q : Pattern) (selected : d302072 q = 0) : d303745 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302072, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302072, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302073 q = 0) : d303746 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302073, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302073, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302074 q = 0) : d303747 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302074, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31304 q selected
    | true =>
      simp only [d302074, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302075 q = 0) : d303748 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302075, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302075, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d302076 q = 0) : d303749 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302076, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302076, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d302077 q = 0) : d303750 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302077, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302077, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d302078 q = 0) : d303751 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302078, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d302078, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d302079 q = 0) : d303752 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d302079, d303752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302079, d303752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro31306 (p : Pattern) (selected : d302085 p = 0) : d303758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302067 q = 0) : d303740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302068 q = 0) : d303741 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302069 q = 0) : d303742 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302069, d303742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302069, d303742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302082 q = 0) : d303755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302083 q = 0) : d303756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302084 q = 0) : d303757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302084, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302084, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302085 q = 0) : d303758 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302085, d303758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302085, d303758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31307 (p : Pattern) (selected : d302087 p = 0) : d303760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302067 q = 0) : d303740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302068 q = 0) : d303741 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302082 q = 0) : d303755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302083 q = 0) : d303756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302084 q = 0) : d303757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302084, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302084, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302086 q = 0) : d303759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302086, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302086, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302087 q = 0) : d303760 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302087, d303760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302087, d303760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31308 (p : Pattern) (selected : d302091 p = 0) : d303764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302071 q = 0) : d303744 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302071, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302071, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31304 q selected
  have h2 (q : Pattern) (selected : d302072 q = 0) : d303745 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302072, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302072, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302073 q = 0) : d303746 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302073, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302073, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302074 q = 0) : d303747 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302074, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31304 q selected
    | true =>
      simp only [d302074, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302075 q = 0) : d303748 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302075, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302075, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302076 q = 0) : d303749 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302076, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302076, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302077 q = 0) : d303750 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302077, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302077, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302078 q = 0) : d303751 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302078, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302078, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302091 q = 0) : d303764 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d302091, d303764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302091, d303764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro31309 (p : Pattern) (selected : d302097 p = 0) : d303770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302082 q = 0) : d303755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302083 q = 0) : d303756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302086 q = 0) : d303759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302086, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302086, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302092 q = 0) : d303765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302092, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31308 q selected
    | true =>
      simp only [d302092, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302093 q = 0) : d303766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302093, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302093, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302094 q = 0) : d303767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302094, d303767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302094, d303767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302095 q = 0) : d303768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302095, d303768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302095, d303768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302096 q = 0) : d303769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302096, d303769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302096, d303769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302097 q = 0) : d303770 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302097, d303770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302097, d303770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31310 (p : Pattern) (selected : d302104 p = 0) : d303777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302088 q = 0) : d303761 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302088, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31306 q selected
    | true =>
      simp only [d302088, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31307 q selected
  have h2 (q : Pattern) (selected : d302089 q = 0) : d303762 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302089, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302089, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302090 q = 0) : d303763 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302090, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302090, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302098 q = 0) : d303771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31307 q selected
    | true =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31309 q selected
  have h5 (q : Pattern) (selected : d302099 q = 0) : d303772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302100 q = 0) : d303773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302101 q = 0) : d303774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302101, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302101, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302102 q = 0) : d303775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302102, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302102, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302103 q = 0) : d303776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302103, d303776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302103, d303776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302104 q = 0) : d303777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302104, d303777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302104, d303777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31311 (p : Pattern) (selected : d302108 p = 0) : d303781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302098 q = 0) : d303771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31307 q selected
    | true =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31309 q selected
  have h2 (q : Pattern) (selected : d302099 q = 0) : d303772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302100 q = 0) : d303773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302102 q = 0) : d303775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302102, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302102, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302107 q = 0) : d303780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302107, d303780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302107, d303780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302108 q = 0) : d303781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302108, d303781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302108, d303781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31312 (p : Pattern) (selected : d302114 p = 0) : d303787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302111 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302112 q = 0) : d303785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302113 q = 0) : d303786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302113, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302113, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302114 q = 0) : d303787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302114, d303787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302114, d303787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31313 (p : Pattern) (selected : d302118 p = 0) : d303791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302115 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302116 q = 0) : d303789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302117 q = 0) : d303790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302117, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302117, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302118 q = 0) : d303791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302118, d303791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302118, d303791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31314 (p : Pattern) (selected : d302124 p = 0) : d303797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302119 q = 0) : d303792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302119, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31312 q selected
    | true =>
      simp only [d302119, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31313 q selected
  have h2 (q : Pattern) (selected : d302120 q = 0) : d303793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302120, d303793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302120, d303793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302121 q = 0) : d303794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302121, d303794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302121, d303794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302122 q = 0) : d303795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302122, d303795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302122, d303795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302123 q = 0) : d303796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302123, d303796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302123, d303796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302124 q = 0) : d303797 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302124, d303797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302124, d303797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31315 (p : Pattern) (selected : d302127 p = 0) : d303800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302111 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302112 q = 0) : d303785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302113 q = 0) : d303786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302113, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302113, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302127 q = 0) : d303800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302127, d303800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302127, d303800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31316 (p : Pattern) (selected : d302128 p = 0) : d303801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302115 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302116 q = 0) : d303789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302117 q = 0) : d303790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302117, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302117, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302128 q = 0) : d303801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302128, d303801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302128, d303801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31317 (p : Pattern) (selected : d302134 p = 0) : d303807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302119 q = 0) : d303792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302119, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31312 q selected
    | true =>
      simp only [d302119, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31313 q selected
  have h2 (q : Pattern) (selected : d302120 q = 0) : d303793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302120, d303793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302120, d303793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302121 q = 0) : d303794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302121, d303794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302121, d303794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302122 q = 0) : d303795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302122, d303795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302122, d303795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302123 q = 0) : d303796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302123, d303796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302123, d303796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302129 q = 0) : d303802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302129, d303802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31315 q selected
    | true =>
      simp only [d302129, d303802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31316 q selected
  have h7 (q : Pattern) (selected : d302130 q = 0) : d303803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302130, d303803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302130, d303803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302131 q = 0) : d303804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302131, d303804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302131, d303804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302132 q = 0) : d303805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302132, d303805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302132, d303805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302133 q = 0) : d303806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302133, d303806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302133, d303806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302134 q = 0) : d303807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302134, d303807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302134, d303807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31318 (p : Pattern) (selected : d302139 p = 0) : d303812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302111 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302112 q = 0) : d303785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302138 q = 0) : d303811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302138, d303811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302138, d303811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302139 q = 0) : d303812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302139, d303812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302139, d303812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31319 (p : Pattern) (selected : d302141 p = 0) : d303814 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302115 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302116 q = 0) : d303789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302140 q = 0) : d303813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302140, d303813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302140, d303813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302141 q = 0) : d303814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302141, d303814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302141, d303814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31320 (p : Pattern) (selected : d302148 p = 0) : d303821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302111 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302146 q = 0) : d303819 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302146, d303819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302146, d303819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302147 q = 0) : d303820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302147, d303820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302147, d303820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302148 q = 0) : d303821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302148, d303821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302148, d303821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31321 (p : Pattern) (selected : d302151 p = 0) : d303824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302115 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302149 q = 0) : d303822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302149, d303822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302149, d303822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302150 q = 0) : d303823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302150, d303823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302150, d303823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302151 q = 0) : d303824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302151, d303824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302151, d303824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31322 (p : Pattern) (selected : d302155 p = 0) : d303828 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302067 q = 0) : d303740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302068 q = 0) : d303741 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302069 q = 0) : d303742 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302069, d303742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302069, d303742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302155 q = 0) : d303828 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302155, d303828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302155, d303828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31323 (p : Pattern) (selected : d302161 p = 0) : d303834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302156 q = 0) : d303829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302156, d303829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31322 q selected
    | true =>
      simp only [d302156, d303829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31306 q selected
  have h2 (q : Pattern) (selected : d302157 q = 0) : d303830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302157, d303830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302157, d303830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302158 q = 0) : d303831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302158, d303831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302158, d303831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302088 q = 0) : d303761 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302088, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31306 q selected
    | true =>
      simp only [d302088, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31307 q selected
  have h5 (q : Pattern) (selected : d302089 q = 0) : d303762 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302089, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302089, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302090 q = 0) : d303763 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302090, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302090, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302159 q = 0) : d303832 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302159, d303832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302159, d303832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302098 q = 0) : d303771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31307 q selected
    | true =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31309 q selected
  have h9 (q : Pattern) (selected : d302099 q = 0) : d303772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302100 q = 0) : d303773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302101 q = 0) : d303774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302101, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302101, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d302160 q = 0) : d303833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302160, d303833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302160, d303833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302161 q = 0) : d303834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302161, d303834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302161, d303834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro31324 (p : Pattern) (selected : d302167 p = 0) : d303840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302162 q = 0) : d303835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302162, d303835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31323 q selected
    | true =>
      simp only [d302162, d303835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302163 q = 0) : d303836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302163, d303836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302163, d303836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302164 q = 0) : d303837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302164, d303837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302164, d303837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302165 q = 0) : d303838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302165, d303838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302165, d303838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302166 q = 0) : d303839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302166, d303839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302166, d303839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302167 q = 0) : d303840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302167, d303840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302167, d303840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31325 (p : Pattern) (selected : d302169 p = 0) : d303728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 0) : d52964 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, d52964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302169 q = 0) : d303728 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d302169, d303728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302169, d303728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro31326 (p : Pattern) (selected : d302172 p = 0) : d303731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 0) : d52106 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, d52106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2163 q = 0) : d53276 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2163, d53276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302172 q = 0) : d303731 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d302172, d303731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302172, d303731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro31327 (p : Pattern) (selected : d302178 p = 0) : d303737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302170 q = 0) : d303729 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302170, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302170, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31325 q selected
  have h2 (q : Pattern) (selected : d302171 q = 0) : d303730 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302171, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302171, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302173 q = 0) : d303732 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302173, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31326 q selected
    | true =>
      simp only [d302173, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302174 q = 0) : d303733 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302174, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302174, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302175 q = 0) : d303734 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302175, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302175, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302176 q = 0) : d303735 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302176, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302176, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302177 q = 0) : d303736 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302177, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302177, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302178 q = 0) : d303737 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d302178, d303737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302178, d303737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31328 (p : Pattern) (selected : d302184 p = 0) : d303743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2182 q = 0) : d53295 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d2182, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2182, d53295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302184 q = 0) : d303743 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d302184, d303743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302184, d303743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31329 (p : Pattern) (selected : d302193 p = 0) : d303752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302170 q = 0) : d303729 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302170, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302170, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31325 q selected
  have h2 (q : Pattern) (selected : d302171 q = 0) : d303730 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302171, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302171, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302173 q = 0) : d303732 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302173, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31326 q selected
    | true =>
      simp only [d302173, d303732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302174 q = 0) : d303733 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302174, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302174, d303733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302175 q = 0) : d303734 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302175, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302175, d303734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302176 q = 0) : d303735 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302176, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302176, d303735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302177 q = 0) : d303736 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302177, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302177, d303736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302185 q = 0) : d303744 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302185, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302185, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31328 q selected
  have h9 (q : Pattern) (selected : d302186 q = 0) : d303745 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302186, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302186, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302187 q = 0) : d303746 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302187, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302187, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302188 q = 0) : d303747 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302188, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31328 q selected
    | true =>
      simp only [d302188, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302189 q = 0) : d303748 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302189, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302189, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d302190 q = 0) : d303749 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302190, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302190, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d302191 q = 0) : d303750 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302191, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302191, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d302192 q = 0) : d303751 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302192, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d302192, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d302193 q = 0) : d303752 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d302193, d303752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302193, d303752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro31330 (p : Pattern) (selected : d302199 p = 0) : d303758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302179 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31327 q selected
    | true =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302180 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302181 q = 0) : d303740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302181, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302181, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302182 q = 0) : d303741 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302182, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302182, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302183 q = 0) : d303742 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302183, d303742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302183, d303742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302194 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
    | true =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302195 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302196 q = 0) : d303755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302196, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302196, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302197 q = 0) : d303756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302197, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302197, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302198 q = 0) : d303757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302198, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302198, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302199 q = 0) : d303758 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302199, d303758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302199, d303758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31331 (p : Pattern) (selected : d302201 p = 0) : d303760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302179 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31327 q selected
    | true =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302180 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302181 q = 0) : d303740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302181, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302181, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302182 q = 0) : d303741 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302182, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302182, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302194 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
    | true =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302195 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302196 q = 0) : d303755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302196, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302196, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302197 q = 0) : d303756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302197, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302197, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302198 q = 0) : d303757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302198, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302198, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302200 q = 0) : d303759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302200, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302200, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302201 q = 0) : d303760 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302201, d303760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302201, d303760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31332 (p : Pattern) (selected : d302205 p = 0) : d303764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302185 q = 0) : d303744 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302185, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302185, d303744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31328 q selected
  have h2 (q : Pattern) (selected : d302186 q = 0) : d303745 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302186, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302186, d303745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302187 q = 0) : d303746 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302187, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302187, d303746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302188 q = 0) : d303747 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302188, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31328 q selected
    | true =>
      simp only [d302188, d303747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302189 q = 0) : d303748 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302189, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302189, d303748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302190 q = 0) : d303749 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302190, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302190, d303749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302191 q = 0) : d303750 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302191, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302191, d303750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302192 q = 0) : d303751 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302192, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302192, d303751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302205 q = 0) : d303764 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d302205, d303764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302205, d303764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro31333 (p : Pattern) (selected : d302211 p = 0) : d303770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302194 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
    | true =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302195 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302196 q = 0) : d303755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302196, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302196, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302197 q = 0) : d303756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302197, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302197, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302200 q = 0) : d303759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302200, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302200, d303759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302206 q = 0) : d303765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302206, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31332 q selected
    | true =>
      simp only [d302206, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302207 q = 0) : d303766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302207, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302207, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302208 q = 0) : d303767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302208, d303767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302208, d303767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302209 q = 0) : d303768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302209, d303768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302209, d303768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302210 q = 0) : d303769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302210, d303769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302210, d303769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302211 q = 0) : d303770 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302211, d303770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302211, d303770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31334 (p : Pattern) (selected : d302218 p = 0) : d303777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302202 q = 0) : d303761 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302202, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31330 q selected
    | true =>
      simp only [d302202, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31331 q selected
  have h2 (q : Pattern) (selected : d302203 q = 0) : d303762 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302203, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302203, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302204 q = 0) : d303763 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302204, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302204, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302212 q = 0) : d303771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302212, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31331 q selected
    | true =>
      simp only [d302212, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31333 q selected
  have h5 (q : Pattern) (selected : d302213 q = 0) : d303772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302213, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302213, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302214 q = 0) : d303773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302214, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302214, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302215 q = 0) : d303774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302215, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302215, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302216 q = 0) : d303775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302216, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302216, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302217 q = 0) : d303776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302217, d303776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302217, d303776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302218 q = 0) : d303777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302218, d303777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302218, d303777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31335 (p : Pattern) (selected : d302222 p = 0) : d303781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302212 q = 0) : d303771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302212, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31331 q selected
    | true =>
      simp only [d302212, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31333 q selected
  have h2 (q : Pattern) (selected : d302213 q = 0) : d303772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302213, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302213, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302214 q = 0) : d303773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302214, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302214, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302216 q = 0) : d303775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302216, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302216, d303775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302221 q = 0) : d303780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302221, d303780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302221, d303780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302222 q = 0) : d303781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302222, d303781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302222, d303781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31336 (p : Pattern) (selected : d302228 p = 0) : d303787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302219 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302219, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31334 q selected
    | true =>
      simp only [d302219, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302220 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302220, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302220, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302223 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31335 q selected
    | true =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302224 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302225 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302225, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302225, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302226 q = 0) : d303785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302226, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302226, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302227 q = 0) : d303786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302227, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302227, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302228 q = 0) : d303787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302228, d303787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302228, d303787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31337 (p : Pattern) (selected : d302232 p = 0) : d303791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302223 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31335 q selected
    | true =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302224 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302229 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302229, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302229, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302230 q = 0) : d303789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302230, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302230, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302231 q = 0) : d303790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302231, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302231, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302232 q = 0) : d303791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302232, d303791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302232, d303791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31338 (p : Pattern) (selected : d302238 p = 0) : d303846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302056 q = 0) : d303729 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d302056, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302056, d303729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31301 q selected
  have h2 (q : Pattern) (selected : d302057 q = 0) : d303730 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d302057, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302057, d303730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302235 q = 0) : d303843 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d302235, d303843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302235, d303843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302236 q = 0) : d303844 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d302236, d303844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302236, d303844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302237 q = 0) : d303845 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d302237, d303845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302237, d303845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302238 q = 0) : d303846 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d302238, d303846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302238, d303846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31339 (p : Pattern) (selected : d302244 p = 0) : d303852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302067 q = 0) : d303740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302067, d303740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302068 q = 0) : d303741 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302068, d303741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302082 q = 0) : d303755 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302082, d303755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302083 q = 0) : d303756 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302083, d303756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302084 q = 0) : d303757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302084, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302084, d303757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302239 q = 0) : d303847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31338 q selected
    | true =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302240 q = 0) : d303848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302241 q = 0) : d303849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302241, d303849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302241, d303849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302242 q = 0) : d303850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302242, d303850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302242, d303850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d302243 q = 0) : d303851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302243, d303851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302243, d303851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d302244 q = 0) : d303852 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302244, d303852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302244, d303852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31340 (p : Pattern) (selected : d302245 p = 0) : d303853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302239 q = 0) : d303847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31338 q selected
    | true =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302240 q = 0) : d303848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302241 q = 0) : d303849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302241, d303849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302241, d303849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302242 q = 0) : d303850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302242, d303850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302242, d303850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302243 q = 0) : d303851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302243, d303851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302243, d303851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302245 q = 0) : d303853 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302245, d303853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302245, d303853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31341 (p : Pattern) (selected : d302251 p = 0) : d303859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302088 q = 0) : d303761 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302088, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31306 q selected
    | true =>
      simp only [d302088, d303761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31307 q selected
  have h2 (q : Pattern) (selected : d302089 q = 0) : d303762 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302089, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302089, d303762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302090 q = 0) : d303763 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302090, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302090, d303763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302098 q = 0) : d303771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31307 q selected
    | true =>
      simp only [d302098, d303771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31309 q selected
  have h5 (q : Pattern) (selected : d302099 q = 0) : d303772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302099, d303772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302100 q = 0) : d303773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302100, d303773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302101 q = 0) : d303774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302101, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302101, d303774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302246 q = 0) : d303854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302246, d303854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31339 q selected
    | true =>
      simp only [d302246, d303854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31340 q selected
  have h9 (q : Pattern) (selected : d302247 q = 0) : d303855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302247, d303855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302247, d303855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302248 q = 0) : d303856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302248, d303856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302248, d303856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302249 q = 0) : d303857 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302249, d303857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302249, d303857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302250 q = 0) : d303858 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302250, d303858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302250, d303858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302251 q = 0) : d303859 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302251, d303859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302251, d303859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro31342 (p : Pattern) (selected : d302257 p = 0) : d303865 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302252 q = 0) : d303860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302252, d303860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31341 q selected
    | true =>
      simp only [d302252, d303860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302253 q = 0) : d303861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302253, d303861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302253, d303861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302254 q = 0) : d303862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302254, d303862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302254, d303862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302255 q = 0) : d303863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302255, d303863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302255, d303863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302256 q = 0) : d303864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302256, d303864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302256, d303864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302257 q = 0) : d303865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302257, d303865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302257, d303865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31343 (p : Pattern) (selected : d302263 p = 0) : d303871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302142 q = 0) : d303815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302142, d303815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31318 q selected
    | true =>
      simp only [d302142, d303815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31319 q selected
  have h2 (q : Pattern) (selected : d302143 q = 0) : d303816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302143, d303816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302143, d303816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302144 q = 0) : d303817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302144, d303817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302144, d303817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302145 q = 0) : d303818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302145, d303818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302145, d303818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302152 q = 0) : d303825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302152, d303825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31320 q selected
    | true =>
      simp only [d302152, d303825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31321 q selected
  have h6 (q : Pattern) (selected : d302153 q = 0) : d303826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302153, d303826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302153, d303826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302154 q = 0) : d303827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302154, d303827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302154, d303827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302168 q = 0) : d303841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302168, d303841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31324 q selected
    | true =>
      simp only [d302168, d303841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31312 q selected
  have h9 (q : Pattern) (selected : d302233 q = 0) : d303792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302233, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31336 q selected
    | true =>
      simp only [d302233, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31337 q selected
  have h10 (q : Pattern) (selected : d302234 q = 0) : d303842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302234, d303842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302234, d303842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302258 q = 0) : d303866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302258, d303866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31342 q selected
    | true =>
      simp only [d302258, d303866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302259 q = 0) : d303867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302259, d303867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302259, d303867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d302260 q = 0) : d303868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302260, d303868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302260, d303868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302261 q = 0) : d303869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302261, d303869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302261, d303869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d302262 q = 0) : d303870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302262, d303870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302262, d303870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d302263 q = 0) : d303871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302263, d303871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302263, d303871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro31344 (p : Pattern) (selected : d302264 p = 0) : d303872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302111 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302112 q = 0) : d303785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302112, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302138 q = 0) : d303811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302138, d303811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302138, d303811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302264 q = 0) : d303872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302264, d303872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302264, d303872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31345 (p : Pattern) (selected : d302265 p = 0) : d303873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302115 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302116 q = 0) : d303789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302116, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302140 q = 0) : d303813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302140, d303813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302140, d303813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302265 q = 0) : d303873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302265, d303873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302265, d303873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31346 (p : Pattern) (selected : d302270 p = 0) : d303878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302111 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302111, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302146 q = 0) : d303819 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302146, d303819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302146, d303819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302147 q = 0) : d303820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302147, d303820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302147, d303820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302270 q = 0) : d303878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302270, d303878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302270, d303878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31347 (p : Pattern) (selected : d302271 p = 0) : d303879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302109 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31311 q selected
    | true =>
      simp only [d302109, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302110 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302110, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302115 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302115, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302149 q = 0) : d303822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302149, d303822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302149, d303822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302150 q = 0) : d303823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302150, d303823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302150, d303823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302271 q = 0) : d303879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302271, d303879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302271, d303879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31348 (p : Pattern) (selected : d302275 p = 0) : d303883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302162 q = 0) : d303835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302162, d303835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31323 q selected
    | true =>
      simp only [d302162, d303835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302163 q = 0) : d303836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302163, d303836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302163, d303836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302105 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31310 q selected
    | true =>
      simp only [d302105, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302106 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302106, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302164 q = 0) : d303837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302164, d303837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302164, d303837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302165 q = 0) : d303838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302165, d303838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302165, d303838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302166 q = 0) : d303839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302166, d303839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302166, d303839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302275 q = 0) : d303883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302275, d303883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302275, d303883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31349 (p : Pattern) (selected : d302277 p = 0) : d303800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302219 q = 0) : d303778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302219, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31334 q selected
    | true =>
      simp only [d302219, d303778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302220 q = 0) : d303779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302220, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302220, d303779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302223 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31335 q selected
    | true =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302224 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302225 q = 0) : d303784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302225, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302225, d303784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302226 q = 0) : d303785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302226, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302226, d303785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302227 q = 0) : d303786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302227, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302227, d303786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302277 q = 0) : d303800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302277, d303800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302277, d303800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31350 (p : Pattern) (selected : d302278 p = 0) : d303801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302223 q = 0) : d303782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31335 q selected
    | true =>
      simp only [d302223, d303782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302224 q = 0) : d303783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302224, d303783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302229 q = 0) : d303788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302229, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302229, d303788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302230 q = 0) : d303789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302230, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302230, d303789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302231 q = 0) : d303790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302231, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302231, d303790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302278 q = 0) : d303801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302278, d303801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302278, d303801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31351 (p : Pattern) (selected : d302281 p = 0) : d303886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302252 q = 0) : d303860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302252, d303860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31341 q selected
    | true =>
      simp only [d302252, d303860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302253 q = 0) : d303861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302253, d303861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302253, d303861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302254 q = 0) : d303862 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302254, d303862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302254, d303862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302255 q = 0) : d303863 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302255, d303863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302255, d303863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302256 q = 0) : d303864 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302256, d303864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302256, d303864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302281 q = 0) : d303886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302281, d303886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302281, d303886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31352 (p : Pattern) (selected : d302287 p = 0) : d303892 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302142 q = 0) : d303815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302142, d303815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31318 q selected
    | true =>
      simp only [d302142, d303815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31319 q selected
  have h2 (q : Pattern) (selected : d302143 q = 0) : d303816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302143, d303816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302143, d303816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302144 q = 0) : d303817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302144, d303817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302144, d303817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302145 q = 0) : d303818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302145, d303818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302145, d303818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302152 q = 0) : d303825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302152, d303825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31320 q selected
    | true =>
      simp only [d302152, d303825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31321 q selected
  have h6 (q : Pattern) (selected : d302153 q = 0) : d303826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302153, d303826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302153, d303826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302154 q = 0) : d303827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302154, d303827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302154, d303827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302168 q = 0) : d303841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302168, d303841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31324 q selected
    | true =>
      simp only [d302168, d303841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31312 q selected
  have h9 (q : Pattern) (selected : d302233 q = 0) : d303792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302233, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31336 q selected
    | true =>
      simp only [d302233, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31337 q selected
  have h10 (q : Pattern) (selected : d302234 q = 0) : d303842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302234, d303842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302234, d303842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302258 q = 0) : d303866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302258, d303866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31342 q selected
    | true =>
      simp only [d302258, d303866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302259 q = 0) : d303867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302259, d303867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302259, d303867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d302260 q = 0) : d303868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302260, d303868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302260, d303868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302261 q = 0) : d303869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302261, d303869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302261, d303869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d302262 q = 0) : d303870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302262, d303870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302262, d303870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d302266 q = 0) : d303874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302266, d303874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31344 q selected
    | true =>
      simp only [d302266, d303874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31345 q selected
  have h17 (q : Pattern) (selected : d302267 q = 0) : d303875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302267, d303875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302267, d303875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d302268 q = 0) : d303876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302268, d303876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d302268, d303876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d302269 q = 0) : d303877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302269, d303877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302269, d303877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d302272 q = 0) : d303880 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302272, d303880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31346 q selected
    | true =>
      simp only [d302272, d303880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31347 q selected
  have h21 (q : Pattern) (selected : d302273 q = 0) : d303881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302273, d303881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302273, d303881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d302274 q = 0) : d303882 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302274, d303882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d302274, d303882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d302276 q = 0) : d303884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302276, d303884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31348 q selected
    | true =>
      simp only [d302276, d303884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31315 q selected
  have h24 (q : Pattern) (selected : d302279 q = 0) : d303802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302279, d303802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31349 q selected
    | true =>
      simp only [d302279, d303802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31350 q selected
  have h25 (q : Pattern) (selected : d302280 q = 0) : d303885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302280, d303885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d302280, d303885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d302282 q = 0) : d303887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302282, d303887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31351 q selected
    | true =>
      simp only [d302282, d303887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d302283 q = 0) : d303888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302283, d303888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d302283, d303888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d302284 q = 0) : d303889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302284, d303889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d302284, d303889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d302285 q = 0) : d303890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302285, d303890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d302285, d303890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d302286 q = 0) : d303891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302286, d303891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d302286, d303891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d302287 q = 0) : d303892 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302287, d303892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d302287, d303892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro31353 (p : Pattern) (selected : d302294 p = 0) : d303899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302119 q = 0) : d303792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302119, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31312 q selected
    | true =>
      simp only [d302119, d303792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31313 q selected
  have h2 (q : Pattern) (selected : d302120 q = 0) : d303793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302120, d303793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302120, d303793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302121 q = 0) : d303794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302121, d303794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302121, d303794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302122 q = 0) : d303795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302122, d303795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302122, d303795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302123 q = 0) : d303796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302123, d303796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302123, d303796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302289 q = 0) : d303894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302289, d303894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31313 q selected
    | true =>
      simp only [d302289, d303894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302290 q = 0) : d303895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302290, d303895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302290, d303895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302291 q = 0) : d303896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302291, d303896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302291, d303896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302292 q = 0) : d303897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302292, d303897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302292, d303897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302293 q = 0) : d303898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302293, d303898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302293, d303898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302294 q = 0) : d303899 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302294, d303899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302294, d303899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31354 (p : Pattern) (selected : d302300 p = 0) : d303905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302289 q = 0) : d303894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302289, d303894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31313 q selected
    | true =>
      simp only [d302289, d303894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302290 q = 0) : d303895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302290, d303895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302290, d303895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302291 q = 0) : d303896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302291, d303896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302291, d303896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302292 q = 0) : d303897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302292, d303897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302292, d303897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302293 q = 0) : d303898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302293, d303898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302293, d303898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302295 q = 0) : d303900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302295, d303900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31316 q selected
    | true =>
      simp only [d302295, d303900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302296 q = 0) : d303901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302296, d303901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302296, d303901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302297 q = 0) : d303902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302297, d303902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302297, d303902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302298 q = 0) : d303903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302298, d303903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302298, d303903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302299 q = 0) : d303904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302299, d303904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302299, d303904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302300 q = 0) : d303905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302300, d303905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302300, d303905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31355 (p : Pattern) (selected : d302307 p = 0) : d303912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302276 q = 0) : d303884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302276, d303884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31348 q selected
    | true =>
      simp only [d302276, d303884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31315 q selected
  have h2 (q : Pattern) (selected : d302279 q = 0) : d303802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302279, d303802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31349 q selected
    | true =>
      simp only [d302279, d303802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31350 q selected
  have h3 (q : Pattern) (selected : d302280 q = 0) : d303885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302280, d303885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302280, d303885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302282 q = 0) : d303887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302282, d303887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31351 q selected
    | true =>
      simp only [d302282, d303887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302283 q = 0) : d303888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302283, d303888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302283, d303888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302284 q = 0) : d303889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302284, d303889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302284, d303889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302305 q = 0) : d303910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302305, d303910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302305, d303910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302306 q = 0) : d303911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302306, d303911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302306, d303911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302307 q = 0) : d303912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302307, d303912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302307, d303912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro31356 (p : Pattern) (selected : d302309 p = 0) : d303914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302295 q = 0) : d303900 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302295, d303900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31316 q selected
    | true =>
      simp only [d302295, d303900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302296 q = 0) : d303901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302296, d303901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302296, d303901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302297 q = 0) : d303902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302297, d303902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302297, d303902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302298 q = 0) : d303903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302298, d303903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302298, d303903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302299 q = 0) : d303904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302299, d303904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302299, d303904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302309 q = 0) : d303914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302309, d303914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302309, d303914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31357 (p : Pattern) (selected : d302320 p = 0) : d303925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302315 q = 0) : d303920 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
  have h2 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302316 q = 0) : d303921 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302317 q = 0) : d303922 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302318 q = 0) : d303923 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302319 q = 0) : d303924 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302319, d303924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302319, d303924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302320 q = 0) : d303925 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302320, d303925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302320, d303925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31358 (p : Pattern) (selected : d302326 p = 0) : d303931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302315 q = 0) : d303920 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
  have h2 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302316 q = 0) : d303921 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302317 q = 0) : d303922 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302318 q = 0) : d303923 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302319 q = 0) : d303924 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302319, d303924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302319, d303924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302321 q = 0) : d303926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
  have h9 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302322 q = 0) : d303927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302323 q = 0) : d303928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302324 q = 0) : d303929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d302325 q = 0) : d303930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302325, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302325, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d302326 q = 0) : d303931 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302326, d303931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302326, d303931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31359 (p : Pattern) (selected : d302331 p = 0) : d303936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302315 q = 0) : d303920 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
  have h2 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302316 q = 0) : d303921 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302317 q = 0) : d303922 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302318 q = 0) : d303923 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302321 q = 0) : d303926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
  have h8 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302322 q = 0) : d303927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302323 q = 0) : d303928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d302324 q = 0) : d303929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d302325 q = 0) : d303930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302325, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302325, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302330 q = 0) : d303935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302330, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302330, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d302331 q = 0) : d303936 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302331, d303936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302331, d303936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31360 (p : Pattern) (selected : d302341 p = 0) : d303946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302321 q = 0) : d303926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
  have h2 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302322 q = 0) : d303927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302323 q = 0) : d303928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302324 q = 0) : d303929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302330 q = 0) : d303935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302330, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302330, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302336 q = 0) : d303941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302336, d303941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302336, d303941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31308 q selected
  have h9 (q : Pattern) (selected : d302092 q = 0) : d303765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302092, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31308 q selected
    | true =>
      simp only [d302092, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302337 q = 0) : d303942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302337, d303942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302337, d303942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302093 q = 0) : d303766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302093, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302093, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302338 q = 0) : d303943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302338, d303943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302338, d303943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302339 q = 0) : d303944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302339, d303944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302339, d303944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d302340 q = 0) : d303945 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302340, d303945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302340, d303945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d302341 q = 0) : d303946 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302341, d303946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302341, d303946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31361 (p : Pattern) (selected : d302347 p = 0) : d303952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302327 q = 0) : d303932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302327, d303932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31357 q selected
    | true =>
      simp only [d302327, d303932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31358 q selected
  have h2 (q : Pattern) (selected : d302328 q = 0) : d303933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302328, d303933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302328, d303933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302329 q = 0) : d303934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302329, d303934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302329, d303934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302332 q = 0) : d303937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302332, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31358 q selected
    | true =>
      simp only [d302332, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31359 q selected
  have h5 (q : Pattern) (selected : d302333 q = 0) : d303938 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302333, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302333, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302334 q = 0) : d303939 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302334, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302334, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302335 q = 0) : d303940 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302335, d303940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302335, d303940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302342 q = 0) : d303947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31359 q selected
    | true =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31360 q selected
  have h9 (q : Pattern) (selected : d302343 q = 0) : d303948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302344 q = 0) : d303949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302345 q = 0) : d303950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302345, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302345, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d302346 q = 0) : d303951 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302346, d303951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302346, d303951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302347 q = 0) : d303952 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302347, d303952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302347, d303952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro31362 (p : Pattern) (selected : d302352 p = 0) : d303957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302332 q = 0) : d303937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302332, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31358 q selected
    | true =>
      simp only [d302332, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31359 q selected
  have h2 (q : Pattern) (selected : d302333 q = 0) : d303938 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302333, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302333, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302334 q = 0) : d303939 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302334, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302334, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302342 q = 0) : d303947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31359 q selected
    | true =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31360 q selected
  have h5 (q : Pattern) (selected : d302343 q = 0) : d303948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302344 q = 0) : d303949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302345 q = 0) : d303950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302345, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302345, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302350 q = 0) : d303955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302350, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302350, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302351 q = 0) : d303956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302351, d303956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302351, d303956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302352 q = 0) : d303957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302352, d303957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302352, d303957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31363 (p : Pattern) (selected : d302358 p = 0) : d303963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302348 q = 0) : d303953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302348, d303953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31361 q selected
    | true =>
      simp only [d302348, d303953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302349 q = 0) : d303954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302349, d303954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302349, d303954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302353 q = 0) : d303958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302353, d303958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31362 q selected
    | true =>
      simp only [d302353, d303958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302354 q = 0) : d303959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302354, d303959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302354, d303959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302355 q = 0) : d303960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302355, d303960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302355, d303960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302356 q = 0) : d303961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302356, d303961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302356, d303961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302357 q = 0) : d303962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302357, d303962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302357, d303962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302358 q = 0) : d303963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302358, d303963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302358, d303963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31364 (p : Pattern) (selected : d302360 p = 0) : d303965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302342 q = 0) : d303947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31359 q selected
    | true =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31360 q selected
  have h2 (q : Pattern) (selected : d302343 q = 0) : d303948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302344 q = 0) : d303949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302350 q = 0) : d303955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302350, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302350, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302359 q = 0) : d303964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302359, d303964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302359, d303964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302360 q = 0) : d303965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302360, d303965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302360, d303965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31365 (p : Pattern) (selected : d302366 p = 0) : d303971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302353 q = 0) : d303958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302353, d303958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31362 q selected
    | true =>
      simp only [d302353, d303958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302354 q = 0) : d303959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302354, d303959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302354, d303959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302361 q = 0) : d303966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302361, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31364 q selected
    | true =>
      simp only [d302361, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302362 q = 0) : d303967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302362, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302362, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302363 q = 0) : d303968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302363, d303968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302363, d303968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302364 q = 0) : d303969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302364, d303969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302364, d303969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302365 q = 0) : d303970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302365, d303970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302365, d303970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302366 q = 0) : d303971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302366, d303971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302366, d303971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31366 (p : Pattern) (selected : d302378 p = 0) : d303931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302368 q = 0) : d303920 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302368, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302368, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31327 q selected
  have h2 (q : Pattern) (selected : d302179 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31327 q selected
    | true =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302369 q = 0) : d303921 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302369, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302369, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302180 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302370 q = 0) : d303922 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302370, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302370, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302371 q = 0) : d303923 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302371, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302371, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302372 q = 0) : d303924 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302372, d303924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302372, d303924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302373 q = 0) : d303926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302373, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302373, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
  have h9 (q : Pattern) (selected : d302194 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
    | true =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302374 q = 0) : d303927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302374, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302374, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302195 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302375 q = 0) : d303928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302375, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302375, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302376 q = 0) : d303929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302376, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302376, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d302377 q = 0) : d303930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302377, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302377, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d302378 q = 0) : d303931 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302378, d303931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302378, d303931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31367 (p : Pattern) (selected : d302380 p = 0) : d303936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302368 q = 0) : d303920 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302368, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302368, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31327 q selected
  have h2 (q : Pattern) (selected : d302179 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31327 q selected
    | true =>
      simp only [d302179, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302369 q = 0) : d303921 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302369, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302369, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302180 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302180, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302370 q = 0) : d303922 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302370, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302370, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302371 q = 0) : d303923 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302371, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302371, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302373 q = 0) : d303926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302373, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302373, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
  have h8 (q : Pattern) (selected : d302194 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
    | true =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302374 q = 0) : d303927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302374, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302374, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302195 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302375 q = 0) : d303928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302375, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302375, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d302376 q = 0) : d303929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302376, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302376, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d302377 q = 0) : d303930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302377, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302377, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302379 q = 0) : d303935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302379, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302379, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d302380 q = 0) : d303936 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302380, d303936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302380, d303936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31368 (p : Pattern) (selected : d302389 p = 0) : d303946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302373 q = 0) : d303926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302373, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302373, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
  have h2 (q : Pattern) (selected : d302194 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31329 q selected
    | true =>
      simp only [d302194, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302374 q = 0) : d303927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302374, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302374, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302195 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302195, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302375 q = 0) : d303928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302375, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302375, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302376 q = 0) : d303929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302376, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302376, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302379 q = 0) : d303935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302379, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302379, d303935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302384 q = 0) : d303941 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302384, d303941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302384, d303941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31332 q selected
  have h9 (q : Pattern) (selected : d302206 q = 0) : d303765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302206, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31332 q selected
    | true =>
      simp only [d302206, d303765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302385 q = 0) : d303942 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302385, d303942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302385, d303942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302207 q = 0) : d303766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302207, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302207, d303766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302386 q = 0) : d303943 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302386, d303943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302386, d303943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302387 q = 0) : d303944 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302387, d303944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302387, d303944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d302388 q = 0) : d303945 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302388, d303945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302388, d303945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d302389 q = 0) : d303946 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302389, d303946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302389, d303946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31369 (p : Pattern) (selected : d302396 p = 0) : d303957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302381 q = 0) : d303937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302381, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31366 q selected
    | true =>
      simp only [d302381, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31367 q selected
  have h2 (q : Pattern) (selected : d302382 q = 0) : d303938 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302382, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302382, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302383 q = 0) : d303939 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302383, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302383, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302390 q = 0) : d303947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302390, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31367 q selected
    | true =>
      simp only [d302390, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31368 q selected
  have h5 (q : Pattern) (selected : d302391 q = 0) : d303948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302391, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302391, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302392 q = 0) : d303949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302392, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302392, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302393 q = 0) : d303950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302393, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302393, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302394 q = 0) : d303955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302394, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302394, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302395 q = 0) : d303956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302395, d303956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302395, d303956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302396 q = 0) : d303957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302396, d303957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302396, d303957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31370 (p : Pattern) (selected : d302400 p = 0) : d303965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302390 q = 0) : d303947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302390, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31367 q selected
    | true =>
      simp only [d302390, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31368 q selected
  have h2 (q : Pattern) (selected : d302391 q = 0) : d303948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302391, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302391, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302392 q = 0) : d303949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302392, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302392, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302394 q = 0) : d303955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302394, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302394, d303955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302399 q = 0) : d303964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302399, d303964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302399, d303964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302400 q = 0) : d303965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302400, d303965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302400, d303965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31371 (p : Pattern) (selected : d302406 p = 0) : d303971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302397 q = 0) : d303958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302397, d303958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31369 q selected
    | true =>
      simp only [d302397, d303958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302398 q = 0) : d303959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302398, d303959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302398, d303959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302401 q = 0) : d303966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302401, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31370 q selected
    | true =>
      simp only [d302401, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302402 q = 0) : d303967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302402, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302402, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302403 q = 0) : d303968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302403, d303968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302403, d303968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302404 q = 0) : d303969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302404, d303969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302404, d303969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302405 q = 0) : d303970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302405, d303970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302405, d303970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302406 q = 0) : d303971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302406, d303971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302406, d303971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31372 (p : Pattern) (selected : d302410 p = 0) : d303976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302401 q = 0) : d303966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302401, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31370 q selected
    | true =>
      simp only [d302401, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302402 q = 0) : d303967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302402, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302402, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302407 q = 0) : d303973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302407, d303973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302407, d303973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302408 q = 0) : d303974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302408, d303974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302408, d303974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302409 q = 0) : d303975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302409, d303975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302409, d303975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302410 q = 0) : d303976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302410, d303976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302410, d303976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31373 (p : Pattern) (selected : d302418 p = 0) : d303984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302315 q = 0) : d303920 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302315, d303920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
  have h2 (q : Pattern) (selected : d302065 q = 0) : d303738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31303 q selected
    | true =>
      simp only [d302065, d303738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302316 q = 0) : d303921 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302316, d303921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302066 q = 0) : d303739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302066, d303739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302317 q = 0) : d303922 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302317, d303922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302318 q = 0) : d303923 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302318, d303923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302321 q = 0) : d303926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302321, d303926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
  have h8 (q : Pattern) (selected : d302080 q = 0) : d303753 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31305 q selected
    | true =>
      simp only [d302080, d303753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d302322 q = 0) : d303927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302322, d303927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302081 q = 0) : d303754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302081, d303754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d302323 q = 0) : d303928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d302323, d303928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d302324 q = 0) : d303929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302324, d303929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d302325 q = 0) : d303930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302325, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302325, d303930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302413 q = 0) : d303979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302413, d303979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302413, d303979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31338 q selected
  have h15 (q : Pattern) (selected : d302239 q = 0) : d303847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31338 q selected
    | true =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d302414 q = 0) : d303980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302414, d303980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d302414, d303980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d302240 q = 0) : d303848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d302415 q = 0) : d303981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302415, d303981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d302415, d303981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d302416 q = 0) : d303982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302416, d303982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d302416, d303982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d302417 q = 0) : d303983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302417, d303983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d302417, d303983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d302418 q = 0) : d303984 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302418, d303984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302418, d303984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro31374 (p : Pattern) (selected : d302419 p = 0) : d303985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302413 q = 0) : d303979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302413, d303979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302413, d303979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31338 q selected
  have h2 (q : Pattern) (selected : d302239 q = 0) : d303847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31338 q selected
    | true =>
      simp only [d302239, d303847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302414 q = 0) : d303980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302414, d303980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302414, d303980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302240 q = 0) : d303848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302240, d303848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302415 q = 0) : d303981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d302415, d303981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302415, d303981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302416 q = 0) : d303982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d302416, d303982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302416, d303982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d302417 q = 0) : d303983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d302417, d303983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302417, d303983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d302419 q = 0) : d303985 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d302419, d303985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302419, d303985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31375 (p : Pattern) (selected : d302425 p = 0) : d303991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302332 q = 0) : d303937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302332, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31358 q selected
    | true =>
      simp only [d302332, d303937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31359 q selected
  have h2 (q : Pattern) (selected : d302333 q = 0) : d303938 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302333, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302333, d303938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302334 q = 0) : d303939 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302334, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302334, d303939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302342 q = 0) : d303947 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31359 q selected
    | true =>
      simp only [d302342, d303947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31360 q selected
  have h5 (q : Pattern) (selected : d302343 q = 0) : d303948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302343, d303948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302344 q = 0) : d303949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302344, d303949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302345 q = 0) : d303950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302345, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302345, d303950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302420 q = 0) : d303986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d302420, d303986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31373 q selected
    | true =>
      simp only [d302420, d303986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31374 q selected
  have h9 (q : Pattern) (selected : d302421 q = 0) : d303987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d302421, d303987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302421, d303987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302422 q = 0) : d303988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d302422, d303988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302422, d303988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302423 q = 0) : d303989 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d302423, d303989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302423, d303989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d302424 q = 0) : d303990 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d302424, d303990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d302424, d303990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302425 q = 0) : d303991 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d302425, d303991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302425, d303991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro31376 (p : Pattern) (selected : d302431 p = 0) : d303997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302426 q = 0) : d303992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302426, d303992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31375 q selected
    | true =>
      simp only [d302426, d303992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302427 q = 0) : d303993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302427, d303993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302427, d303993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302428 q = 0) : d303994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302428, d303994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302428, d303994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302429 q = 0) : d303995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302429, d303995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302429, d303995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302430 q = 0) : d303996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302430, d303996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302430, d303996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302431 q = 0) : d303997 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302431, d303997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302431, d303997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31377 (p : Pattern) (selected : d302437 p = 0) : d304003 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302367 q = 0) : d303972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302367, d303972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31363 q selected
    | true =>
      simp only [d302367, d303972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31365 q selected
  have h2 (q : Pattern) (selected : d302411 q = 0) : d303977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302411, d303977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31371 q selected
    | true =>
      simp only [d302411, d303977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31372 q selected
  have h3 (q : Pattern) (selected : d302412 q = 0) : d303978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302412, d303978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302412, d303978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302432 q = 0) : d303998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302432, d303998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31376 q selected
    | true =>
      simp only [d302432, d303998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302433 q = 0) : d303999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302433, d303999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302433, d303999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302434 q = 0) : d304000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302434, d304000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302434, d304000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302435 q = 0) : d304001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302435, d304001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302435, d304001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302436 q = 0) : d304002 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302436, d304002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302436, d304002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302437 q = 0) : d304003 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302437, d304003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302437, d304003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro31378 (p : Pattern) (selected : d302442 p = 0) : d303976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302361 q = 0) : d303966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d302361, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31364 q selected
    | true =>
      simp only [d302361, d303966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302362 q = 0) : d303967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d302362, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302362, d303967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302439 q = 0) : d303973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d302439, d303973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302439, d303973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302440 q = 0) : d303974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d302440, d303974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302440, d303974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302441 q = 0) : d303975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302441, d303975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302441, d303975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302442 q = 0) : d303976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302442, d303976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302442, d303976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31379 (p : Pattern) (selected : d302448 p = 0) : d304010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302443 q = 0) : d304005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302443, d304005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31378 q selected
    | true =>
      simp only [d302443, d304005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302444 q = 0) : d304006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302444, d304006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302444, d304006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302445 q = 0) : d304007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302445, d304007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302445, d304007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302446 q = 0) : d304008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302446, d304008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302446, d304008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302447 q = 0) : d304009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302447, d304009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302447, d304009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302448 q = 0) : d304010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302448, d304010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302448, d304010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31380 (p : Pattern) (selected : d302454 p = 0) : d304016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302125 q = 0) : d303798 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302125, d303798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302125, d303798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31314 q selected
  have h2 (q : Pattern) (selected : d302126 q = 0) : d303799 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302126, d303799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302126, d303799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302135 q = 0) : d303808 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302135, d303808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31314 q selected
    | true =>
      simp only [d302135, d303808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31317 q selected
  have h4 (q : Pattern) (selected : d302136 q = 0) : d303809 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302136, d303809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302136, d303809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302137 q = 0) : d303810 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302137, d303810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302137, d303810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302288 q = 0) : d303893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302288, d303893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31343 q selected
    | true =>
      simp only [d302288, d303893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31352 q selected
  have h7 (q : Pattern) (selected : d302301 q = 0) : d303906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302301, d303906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31353 q selected
    | true =>
      simp only [d302301, d303906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31354 q selected
  have h8 (q : Pattern) (selected : d302302 q = 0) : d303907 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302302, d303907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302302, d303907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302303 q = 0) : d303908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302303, d303908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d302303, d303908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d302304 q = 0) : d303909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302304, d303909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302304, d303909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302308 q = 0) : d303913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302308, d303913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302308, d303913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31355 q selected
  have h12 (q : Pattern) (selected : d302310 q = 0) : d303915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302310, d303915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302310, d303915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31356 q selected
  have h13 (q : Pattern) (selected : d302311 q = 0) : d303916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302311, d303916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d302311, d303916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302312 q = 0) : d303917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302312, d303917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302312, d303917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d302313 q = 0) : d303918 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302313, d303918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d302313, d303918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d302314 q = 0) : d303919 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302314, d303919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302314, d303919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d302438 q = 0) : d304004 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302438, d304004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302438, d304004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31377 q selected
  have h18 (q : Pattern) (selected : d302449 q = 0) : d304011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302449, d304011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302449, d304011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31379 q selected
  have h19 (q : Pattern) (selected : d302450 q = 0) : d304012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302450, d304012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d302450, d304012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d302451 q = 0) : d304013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302451, d304013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d302451, d304013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d302452 q = 0) : d304014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302452, d304014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d302452, d304014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d302453 q = 0) : d304015 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302453, d304015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d302453, d304015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d302454 q = 0) : d304016 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d302454, d304016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d302454, d304016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro31381 (p : Pattern) (selected : d302460 p = 0) : d304022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302455 q = 0) : d304017 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d302455, d304017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302455, d304017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31380 q selected
  have h2 (q : Pattern) (selected : d302456 q = 0) : d304018 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d302456, d304018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302456, d304018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302457 q = 0) : d304019 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d302457, d304019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302457, d304019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302458 q = 0) : d304020 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d302458, d304020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302458, d304020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302459 q = 0) : d304021 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d302459, d304021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302459, d304021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302460 q = 0) : d304022 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d302460, d304022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302460, d304022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31382 (p : Pattern) (selected : d302466 p = 0) : d304028 p = 1 := by
  have h0 (q : Pattern) (selected : d300867 q = 0) : d302880 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d300867, d302880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31040 q selected
    | true =>
      simp only [d300867, d302880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31078 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d301192 q = 0) : d303123 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d301192, d303123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301192, d303123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31141 q selected
  have h3 (q : Pattern) (selected : d301193 q = 0) : d303124 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d301193, d303124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301193, d303124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301578 q = 0) : d303392 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d301578, d303392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301578, d303392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31215 q selected
  have h5 (q : Pattern) (selected : d301579 q = 0) : d303393 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d301579, d303393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301579, d303393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301580 q = 0) : d303394 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d301580, d303394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301580, d303394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302051 q = 0) : d303724 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d302051, d303724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302051, d303724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31300 q selected
  have h8 (q : Pattern) (selected : d302052 q = 0) : d303725 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d302052, d303725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302052, d303725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d302053 q = 0) : d303726 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d302053, d303726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302053, d303726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d302054 q = 0) : d303727 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d302054, d303727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302054, d303727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d302461 q = 0) : d304023 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d302461, d304023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302461, d304023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31381 q selected
  have h12 (q : Pattern) (selected : d302462 q = 0) : d304024 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d302462, d304024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302462, d304024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302463 q = 0) : d304025 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d302463, d304025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302463, d304025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d302464 q = 0) : d304026 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d302464, d304026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302464, d304026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d302465 q = 0) : d304027 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d302465, d304027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d302465, d304027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d302466 q = 0) : d304028 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d302466, d304028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d302466, d304028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro31383 (p : Pattern) (selected : d302472 p = 0) : d304034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302467 q = 0) : d304029 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d302467, d304029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31382 q selected
    | true =>
      simp only [d302467, d304029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302468 q = 0) : d304030 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d302468, d304030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302468, d304030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302469 q = 0) : d304031 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d302469, d304031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302469, d304031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302470 q = 0) : d304032 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d302470, d304032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302470, d304032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302471 q = 0) : d304033 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d302471, d304033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302471, d304033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302472 q = 0) : d304034 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d302472, d304034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302472, d304034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31384 (p : Pattern) (selected : d302478 p = 0) : d304040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302473 q = 0) : d304035 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d302473, d304035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31383 q selected
    | true =>
      simp only [d302473, d304035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302474 q = 0) : d304036 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d302474, d304036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302474, d304036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302475 q = 0) : d304037 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d302475, d304037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302475, d304037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302476 q = 0) : d304038 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d302476, d304038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302476, d304038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302477 q = 0) : d304039 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d302477, d304039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302477, d304039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302478 q = 0) : d304040 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d302478, d304040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302478, d304040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31385 (p : Pattern) (selected : d302484 p = 0) : d304046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302479 q = 0) : d304041 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d302479, d304041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31384 q selected
    | true =>
      simp only [d302479, d304041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302480 q = 0) : d304042 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d302480, d304042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302480, d304042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302481 q = 0) : d304043 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d302481, d304043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302481, d304043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302482 q = 0) : d304044 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d302482, d304044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302482, d304044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302483 q = 0) : d304045 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d302483, d304045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302483, d304045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302484 q = 0) : d304046 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d302484, d304046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302484, d304046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31386 (p : Pattern) (selected : d302490 p = 0) : d304052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302485 q = 0) : d304047 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d302485, d304047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31385 q selected
    | true =>
      simp only [d302485, d304047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302486 q = 0) : d304048 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d302486, d304048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302486, d304048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302487 q = 0) : d304049 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d302487, d304049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302487, d304049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302488 q = 0) : d304050 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d302488, d304050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302488, d304050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302489 q = 0) : d304051 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d302489, d304051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302489, d304051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302490 q = 0) : d304052 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d302490, d304052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302490, d304052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31387 (p : Pattern) (selected : d302496 p = 0) : d304058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302491 q = 0) : d304053 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d302491, d304053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31386 q selected
    | true =>
      simp only [d302491, d304053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302492 q = 0) : d304054 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d302492, d304054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302492, d304054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302493 q = 0) : d304055 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d302493, d304055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302493, d304055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302494 q = 0) : d304056 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d302494, d304056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302494, d304056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302495 q = 0) : d304057 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d302495, d304057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302495, d304057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302496 q = 0) : d304058 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d302496, d304058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302496, d304058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31388 (p : Pattern) (selected : d302502 p = 0) : d304064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302497 q = 0) : d304059 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d302497, d304059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31387 q selected
    | true =>
      simp only [d302497, d304059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302498 q = 0) : d304060 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d302498, d304060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302498, d304060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302499 q = 0) : d304061 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d302499, d304061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302499, d304061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302500 q = 0) : d304062 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d302500, d304062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302500, d304062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302501 q = 0) : d304063 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d302501, d304063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302501, d304063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302502 q = 0) : d304064 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d302502, d304064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302502, d304064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31389 (p : Pattern) (selected : d302508 p = 0) : d304070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d302503 q = 0) : d304065 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d302503, d304065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31388 q selected
    | true =>
      simp only [d302503, d304065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d302504 q = 0) : d304066 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d302504, d304066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302504, d304066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d302505 q = 0) : d304067 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d302505, d304067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d302505, d304067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d302506 q = 0) : d304068 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d302506, d304068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302506, d304068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d302507 q = 0) : d304069 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d302507, d304069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302507, d304069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302508 q = 0) : d304070 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d302508, d304070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302508, d304070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31390 (p : Pattern) (selected : d300538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d300538 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d300538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro31391 (p : Pattern) (selected : d300544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300541 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300542 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300543 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300544 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d300544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31392 (p : Pattern) (selected : d300550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
    | true =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300549 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300550 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d300550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31393 (p : Pattern) (selected : d300556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300551 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31392 q selected
    | true =>
      simp only [d300551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300552 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300553 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300554 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300555 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d300555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300556 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d300556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31394 (p : Pattern) (selected : d300562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300557 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31393 q selected
    | true =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300558 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300559 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d300559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300560 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d300560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300561 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d300561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300562 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d300562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31395 (p : Pattern) (selected : d300568 p = 1) : d305743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300505 q = 1) : d300505 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300511 q = 1) : d300511 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d300537 q = 1) : d300537 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d300563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31394 q selected
    | true =>
      simp only [d300563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300564 q = 1) : d305739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300564, d305739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300564, d305739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300428 q = 1) : d300428 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d300565 q = 1) : d305740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300565, d305740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300565, d305740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300566 q = 1) : d305741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300566, d305741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300566, d305741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d300567 q = 1) : d305742 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300567, d305742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300567, d305742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300568 q = 1) : d305743 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300568, d305743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300568, d305743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro31396 (p : Pattern) (selected : d300580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300557 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31393 q selected
    | true =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300558 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300559 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d300559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300560 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d300560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300561 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d300561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d300580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31397 (p : Pattern) (selected : d300586 p = 1) : d305748 p = 1 := by
  have h0 (q : Pattern) (selected : d300505 q = 1) : d300505 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300511 q = 1) : d300511 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300537 q = 1) : d300537 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d300563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31394 q selected
    | true =>
      simp only [d300563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d300564 q = 1) : d305739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300564, d305739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300564, d305739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300428 q = 1) : d300428 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d300565 q = 1) : d305740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300565, d305740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300565, d305740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300566 q = 1) : d305741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300566, d305741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300566, d305741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d300567 q = 1) : d305742 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300567, d305742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300567, d305742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300573 q = 1) : d300573 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d300577 q = 1) : d300577 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d300579 q = 1) : d300579 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d300581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31396 q selected
    | true =>
      simp only [d300581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d300582 q = 1) : d305744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300582, d305744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d300582, d305744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d300435 q = 1) : d300435 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d300583 q = 1) : d305745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300583, d305745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d300583, d305745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d300584 q = 1) : d305746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300584, d305746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300584, d305746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d300585 q = 1) : d305747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300585, d305747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d300585, d305747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d300586 q = 1) : d305748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300586, d305748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300586, d305748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31398 (p : Pattern) (selected : d300595 p = 1) : d305755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300579 q = 1) : d300579 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31396 q selected
    | true =>
      simp only [d300581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300582 q = 1) : d305744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300582, d305744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300582, d305744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300435 q = 1) : d300435 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d300583 q = 1) : d305745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300583, d305745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300583, d305745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300593 q = 1) : d305753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300593, d305753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300593, d305753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300594 q = 1) : d305754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300594, d305754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300594, d305754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300595 q = 1) : d305755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300595, d305755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300595, d305755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31399 (p : Pattern) (selected : d300625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
  have h2 (q : Pattern) (selected : d300545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
    | true =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300622 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300623 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300624 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300625 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d300625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31400 (p : Pattern) (selected : d300631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31399 q selected
    | true =>
      simp only [d300626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300630 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d300630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d300631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31401 (p : Pattern) (selected : d300637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31400 q selected
    | true =>
      simp only [d300632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d300634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d300635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d300636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d300637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31402 (p : Pattern) (selected : d300643 p = 1) : d305765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300619 q = 1) : d300619 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31401 q selected
    | true =>
      simp only [d300638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300639 q = 1) : d305761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300639, d305761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300639, d305761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300469 q = 1) : d300469 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d300640 q = 1) : d305762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300640, d305762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300640, d305762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300641 q = 1) : d305763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300641, d305763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300641, d305763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300642 q = 1) : d305764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300642, d305764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300642, d305764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300643 q = 1) : d305765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300643, d305765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300643, d305765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31403 (p : Pattern) (selected : d300649 p = 1) : d305771 p = 1 := by
  have h0 (q : Pattern) (selected : d300499 q = 1) : d300499 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300587 q = 1) : d305749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d300587, d305749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31395 q selected
    | true =>
      simp only [d300587, d305749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31397 q selected
  have h2 (q : Pattern) (selected : d300589 q = 1) : d300589 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d300590 q = 1) : d305750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d300590, d305750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300590, d305750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d300591 q = 1) : d305751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d300591, d305751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300591, d305751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300592 q = 1) : d305752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d300592, d305752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300592, d305752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300596 q = 1) : d305756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d300596, d305756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300596, d305756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31398 q selected
  have h8 (q : Pattern) (selected : d300597 q = 1) : d305757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d300597, d305757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300597, d305757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d300598 q = 1) : d305758 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d300598, d305758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300598, d305758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d300599 q = 1) : d305759 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d300599, d305759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300599, d305759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d300600 q = 1) : d305760 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d300600, d305760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300600, d305760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d300644 q = 1) : d305766 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d300644, d305766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300644, d305766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31402 q selected
  have h13 (q : Pattern) (selected : d300645 q = 1) : d305767 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d300645, d305767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d300645, d305767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d300646 q = 1) : d305768 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d300646, d305768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300646, d305768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d300647 q = 1) : d305769 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d300647, d305769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d300647, d305769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d300648 q = 1) : d305770 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d300648, d305770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d300648, d305770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d300649 q = 1) : d305771 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d300649, d305771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300649, d305771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro31404 (p : Pattern) (selected : d300655 p = 1) : d305777 p = 1 := by
  have h0 (q : Pattern) (selected : d300484 q = 1) : d300484 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300650 q = 1) : d305772 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d300650, d305772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300650, d305772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31403 q selected
  have h3 (q : Pattern) (selected : d300651 q = 1) : d305773 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d300651, d305773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300651, d305773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300652 q = 1) : d305774 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d300652, d305774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300652, d305774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d300653 q = 1) : d305775 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d300653, d305775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300653, d305775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300654 q = 1) : d305776 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d300654, d305776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300654, d305776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300655 q = 1) : d305777 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d300655, d305777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300655, d305777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro31405 (p : Pattern) (selected : d300721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d340 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d160 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300721 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d300721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31406 (p : Pattern) (selected : d300727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31405 q selected
    | true =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300541 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300542 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d300543 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d300727 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d300727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31407 (p : Pattern) (selected : d300733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31406 q selected
    | true =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
    | true =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300549 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d300733 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d300733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31408 (p : Pattern) (selected : d300739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300734 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31407 q selected
    | true =>
      simp only [d300734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31392 q selected
  have h2 (q : Pattern) (selected : d300735 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300736 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300551 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31392 q selected
    | true =>
      simp only [d300551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300552 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300553 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300554 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300738 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d300738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300739 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d300739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31409 (p : Pattern) (selected : d300745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31408 q selected
    | true =>
      simp only [d300740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300557 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31393 q selected
    | true =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300558 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d300742 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d300742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300743 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d300743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300744 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d300744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d300745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31410 (p : Pattern) (selected : d300757 p = 1) : d305782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300676 q = 1) : d300676 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300682 q = 1) : d300682 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d300720 q = 1) : d300720 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d300746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31409 q selected
    | true =>
      simp only [d300746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31394 q selected
  have h5 (q : Pattern) (selected : d300747 q = 1) : d305778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300747, d305778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300747, d305778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300753 q = 1) : d300753 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d300754 q = 1) : d305779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300754, d305779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300754, d305779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300755 q = 1) : d305780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300755, d305780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300755, d305780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d300756 q = 1) : d305781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300756, d305781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300756, d305781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300757 q = 1) : d305782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300757, d305782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300757, d305782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro31411 (p : Pattern) (selected : d300769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31408 q selected
    | true =>
      simp only [d300740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300557 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31393 q selected
    | true =>
      simp only [d300557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300558 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d300742 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d300742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300743 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d300743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300744 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d300744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300769 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d300769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31412 (p : Pattern) (selected : d300778 p = 1) : d305787 p = 1 := by
  have h0 (q : Pattern) (selected : d300676 q = 1) : d300676 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300682 q = 1) : d300682 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300720 q = 1) : d300720 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d300746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31409 q selected
    | true =>
      simp only [d300746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31394 q selected
  have h4 (q : Pattern) (selected : d300747 q = 1) : d305778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300747, d305778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300747, d305778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d300753 q = 1) : d300753 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d300754 q = 1) : d305779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300754, d305779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300754, d305779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300755 q = 1) : d305780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300755, d305780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300755, d305780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300756 q = 1) : d305781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300756, d305781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300756, d305781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d300762 q = 1) : d300762 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d300766 q = 1) : d300766 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d300768 q = 1) : d300768 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d300770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31411 q selected
    | true =>
      simp only [d300770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31396 q selected
  have h13 (q : Pattern) (selected : d300771 q = 1) : d305783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300771, d305783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300771, d305783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d300774 q = 1) : d300774 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d300775 q = 1) : d305784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300775, d305784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300775, d305784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d300776 q = 1) : d305785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300776, d305785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d300776, d305785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d300777 q = 1) : d305786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300777, d305786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300777, d305786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d300778 q = 1) : d305787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300778, d305787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300778, d305787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro31413 (p : Pattern) (selected : d300787 p = 1) : d305794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300768 q = 1) : d300768 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300770 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31411 q selected
    | true =>
      simp only [d300770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31396 q selected
  have h3 (q : Pattern) (selected : d300771 q = 1) : d305783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300771, d305783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300771, d305783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300774 q = 1) : d300774 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d300775 q = 1) : d305784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300775, d305784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300775, d305784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300785 q = 1) : d305792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300785, d305792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300785, d305792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300786 q = 1) : d305793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300786, d305793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300786, d305793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300787 q = 1) : d305794 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300787, d305794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300787, d305794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31414 (p : Pattern) (selected : d300824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300819 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31406 q selected
  have h2 (q : Pattern) (selected : d300728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31406 q selected
    | true =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300820 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300821 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300822 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
  have h8 (q : Pattern) (selected : d300545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
    | true =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d300622 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d300623 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d300823 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d300624 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d300624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d300824 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d300824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31415 (p : Pattern) (selected : d300830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300825 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31414 q selected
    | true =>
      simp only [d300825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31399 q selected
  have h2 (q : Pattern) (selected : d300826 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300827 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300626 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31399 q selected
    | true =>
      simp only [d300626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300627 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300628 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300828 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300629 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300829 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d300829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300830 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d300830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31416 (p : Pattern) (selected : d300836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300831 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31415 q selected
    | true =>
      simp only [d300831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300832 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d300632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31400 q selected
    | true =>
      simp only [d300632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d300633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d300833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d300833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d300834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d300835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d300836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31417 (p : Pattern) (selected : d300848 p = 1) : d305804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300818 q = 1) : d300818 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d300837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31416 q selected
    | true =>
      simp only [d300837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31401 q selected
  have h3 (q : Pattern) (selected : d300838 q = 1) : d305800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d300838, d305800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300838, d305800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300844 q = 1) : d300844 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d300845 q = 1) : d305801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d300845, d305801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300845, d305801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300846 q = 1) : d305802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300846, d305802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300846, d305802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300847 q = 1) : d305803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d300847, d305803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300847, d305803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300848 q = 1) : d305804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d300848, d305804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300848, d305804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31418 (p : Pattern) (selected : d300860 p = 1) : d305810 p = 1 := by
  have h0 (q : Pattern) (selected : d300670 q = 1) : d300670 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300779 q = 1) : d305788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d300779, d305788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31410 q selected
    | true =>
      simp only [d300779, d305788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31412 q selected
  have h2 (q : Pattern) (selected : d300781 q = 1) : d300781 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d300782 q = 1) : d305789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d300782, d305789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300782, d305789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d300783 q = 1) : d305790 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d300783, d305790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300783, d305790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300784 q = 1) : d305791 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d300784, d305791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300784, d305791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300788 q = 1) : d305795 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d300788, d305795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300788, d305795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31413 q selected
  have h8 (q : Pattern) (selected : d300790 q = 1) : d300790 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d300791 q = 1) : d305796 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d300791, d305796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300791, d305796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300792 q = 1) : d305797 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d300792, d305797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300792, d305797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d300793 q = 1) : d305798 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d300793, d305798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d300793, d305798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d300794 q = 1) : d305799 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d300794, d305799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300794, d305799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d300849 q = 1) : d305805 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d300849, d305805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300849, d305805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31417 q selected
  have h14 (q : Pattern) (selected : d300855 q = 1) : d300855 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d300856 q = 1) : d305806 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d300856, d305806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300856, d305806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d300857 q = 1) : d305807 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d300857, d305807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d300857, d305807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d300858 q = 1) : d305808 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d300858, d305808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d300858, d305808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d300859 q = 1) : d305809 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d300859, d305809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d300859, d305809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d300860 q = 1) : d305810 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d300860, d305810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d300860, d305810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31419 (p : Pattern) (selected : d300866 p = 1) : d305816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300861 q = 1) : d305811 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d300861, d305811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300861, d305811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31418 q selected
  have h2 (q : Pattern) (selected : d300862 q = 1) : d305812 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d300862, d305812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300862, d305812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300863 q = 1) : d305813 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d300863, d305813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300863, d305813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300864 q = 1) : d305814 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d300864, d305814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300864, d305814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d300865 q = 1) : d305815 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d300865, d305815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300865, d305815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300866 q = 1) : d305816 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d300866, d305816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300866, d305816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31420 (p : Pattern) (selected : d300971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1687 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300971 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d300971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro31421 (p : Pattern) (selected : d300975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d339 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d340 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300975 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d300975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro31422 (p : Pattern) (selected : d300981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31405 q selected
    | true =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300974 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300976 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31421 q selected
    | true =>
      simp only [d300976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300977 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d300978 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d300979 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d300980 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d300724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d300541 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d300725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d300726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d300726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d300981 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d300981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d300981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro31423 (p : Pattern) (selected : d300989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31405 q selected
    | true =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300541 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300542 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d300543 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d300989 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d300989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31424 (p : Pattern) (selected : d300995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31422 q selected
    | true =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300984 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300985 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31406 q selected
    | true =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300986 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31423 q selected
    | true =>
      simp only [d300990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d300991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d300991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d300992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d300993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d300993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d300545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
    | true =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d300546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d300547 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d300548 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d300548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d300994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d300995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d300995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31425 (p : Pattern) (selected : d301002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31424 q selected
    | true =>
      simp only [d300996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31407 q selected
  have h2 (q : Pattern) (selected : d300997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300734 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31407 q selected
    | true =>
      simp only [d300734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31392 q selected
  have h5 (q : Pattern) (selected : d300735 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300736 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d300999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301000 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301001 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301002 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31426 (p : Pattern) (selected : d301006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300734 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31407 q selected
    | true =>
      simp only [d300734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31392 q selected
  have h2 (q : Pattern) (selected : d300735 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300736 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301000 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301005 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301006 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31427 (p : Pattern) (selected : d301012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301003 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31425 q selected
    | true =>
      simp only [d301003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301004 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31426 q selected
    | true =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301009 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301010 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301011 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301012 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31428 (p : Pattern) (selected : d301016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31426 q selected
    | true =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31429 (p : Pattern) (selected : d301028 p = 1) : d305822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300911 q = 1) : d300911 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300920 q = 1) : d300920 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d300970 q = 1) : d300970 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d301017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31427 q selected
    | true =>
      simp only [d301017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31428 q selected
  have h5 (q : Pattern) (selected : d301018 q = 1) : d305818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301018, d305818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301018, d305818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301024 q = 1) : d301024 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d301025 q = 1) : d305819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301025, d305819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301025, d305819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301026 q = 1) : d305820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301026, d305820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301026, d305820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301027 q = 1) : d305821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301027, d305821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301027, d305821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301028 q = 1) : d305822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301028, d305822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301028, d305822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro31430 (p : Pattern) (selected : d301042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301003 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31425 q selected
    | true =>
      simp only [d301003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301004 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31426 q selected
    | true =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301009 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301010 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301011 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301042 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31431 (p : Pattern) (selected : d301043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31426 q selected
    | true =>
      simp only [d301007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301013 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301014 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301043 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31432 (p : Pattern) (selected : d301052 p = 1) : d305827 p = 1 := by
  have h0 (q : Pattern) (selected : d300911 q = 1) : d300911 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300920 q = 1) : d300920 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d300970 q = 1) : d300970 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31427 q selected
    | true =>
      simp only [d301017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31428 q selected
  have h4 (q : Pattern) (selected : d301018 q = 1) : d305818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301018, d305818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301018, d305818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301024 q = 1) : d301024 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d301025 q = 1) : d305819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301025, d305819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301025, d305819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301026 q = 1) : d305820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301026, d305820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301026, d305820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301027 q = 1) : d305821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301027, d305821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301027, d305821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301034 q = 1) : d301034 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d301039 q = 1) : d301039 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d301041 q = 1) : d301041 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d301044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31430 q selected
    | true =>
      simp only [d301044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31431 q selected
  have h13 (q : Pattern) (selected : d301045 q = 1) : d305823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301045, d305823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301045, d305823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301048 q = 1) : d301048 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d301049 q = 1) : d305824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301049, d305824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301049, d305824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301050 q = 1) : d305825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301050, d305825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301050, d305825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301051 q = 1) : d305826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301051, d305826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301051, d305826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d301052 q = 1) : d305827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301052, d305827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301052, d305827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro31433 (p : Pattern) (selected : d301072 p = 1) : d305834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301041 q = 1) : d301041 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31430 q selected
    | true =>
      simp only [d301044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31431 q selected
  have h3 (q : Pattern) (selected : d301045 q = 1) : d305823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301045, d305823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301045, d305823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301048 q = 1) : d301048 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301049 q = 1) : d305824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301049, d305824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301049, d305824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301070 q = 1) : d305832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301070, d305832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301070, d305832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301071 q = 1) : d305833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301071, d305833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301071, d305833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301072 q = 1) : d305834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301072, d305834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301072, d305834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31434 (p : Pattern) (selected : d301135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31422 q selected
  have h2 (q : Pattern) (selected : d300982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31422 q selected
    | true =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301127 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301128 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300819 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31406 q selected
  have h8 (q : Pattern) (selected : d300728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31406 q selected
    | true =>
      simp only [d300728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300820 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d300729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d300821 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d300821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d300822 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301129 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31423 q selected
  have h15 (q : Pattern) (selected : d300990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31423 q selected
    | true =>
      simp only [d300990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d300991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d300991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d301132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d301133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d301133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d300620 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
  have h21 (q : Pattern) (selected : d300545 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31391 q selected
    | true =>
      simp only [d300545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d300621 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d300621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d300546 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d300546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d300622 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d300622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d300623 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d300623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d301134 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d301134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d301135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro31435 (p : Pattern) (selected : d301142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31434 q selected
    | true =>
      simp only [d301136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31414 q selected
  have h2 (q : Pattern) (selected : d301137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300825 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31414 q selected
    | true =>
      simp only [d300825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31399 q selected
  have h5 (q : Pattern) (selected : d300826 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300827 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301139 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301140 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301141 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301142 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31436 (p : Pattern) (selected : d301146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300825 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31414 q selected
    | true =>
      simp only [d300825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31399 q selected
  have h2 (q : Pattern) (selected : d300826 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300827 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301140 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301145 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301146 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31437 (p : Pattern) (selected : d301152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31435 q selected
    | true =>
      simp only [d301143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31436 q selected
    | true =>
      simp only [d301147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301151 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301152 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31438 (p : Pattern) (selected : d301156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31436 q selected
    | true =>
      simp only [d301147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301154 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301155 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31439 (p : Pattern) (selected : d301168 p = 1) : d305844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301124 q = 1) : d301124 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31437 q selected
    | true =>
      simp only [d301157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31438 q selected
  have h3 (q : Pattern) (selected : d301158 q = 1) : d305840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301158, d305840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301158, d305840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301164 q = 1) : d301164 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301165 q = 1) : d305841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301165, d305841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301165, d305841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301166 q = 1) : d305842 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301166, d305842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301166, d305842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301167 q = 1) : d305843 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301167, d305843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301167, d305843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301168 q = 1) : d305844 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301168, d305844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301168, d305844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31440 (p : Pattern) (selected : d301185 p = 1) : d305850 p = 1 := by
  have h0 (q : Pattern) (selected : d300903 q = 1) : d300903 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301053 q = 1) : d305828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301053, d305828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31429 q selected
    | true =>
      simp only [d301053, d305828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31432 q selected
  have h2 (q : Pattern) (selected : d301066 q = 1) : d301066 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301067 q = 1) : d305829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301067, d305829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301067, d305829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301068 q = 1) : d305830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301068, d305830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301068, d305830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301069 q = 1) : d305831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301069, d305831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301069, d305831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301073 q = 1) : d305835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301073, d305835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301073, d305835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31433 q selected
  have h8 (q : Pattern) (selected : d301075 q = 1) : d301075 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d301076 q = 1) : d305836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301076, d305836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301076, d305836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301077 q = 1) : d305837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301077, d305837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301077, d305837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d301078 q = 1) : d305838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301078, d305838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301078, d305838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d301079 q = 1) : d305839 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d301079, d305839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301079, d305839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301169 q = 1) : d305845 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301169, d305845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301169, d305845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31439 q selected
  have h14 (q : Pattern) (selected : d301180 q = 1) : d301180 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d301181 q = 1) : d305846 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301181, d305846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301181, d305846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301182 q = 1) : d305847 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301182, d305847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301182, d305847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d301183 q = 1) : d305848 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301183, d305848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301183, d305848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d301184 q = 1) : d305849 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d301184, d305849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d301184, d305849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d301185 q = 1) : d305850 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d301185, d305850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301185, d305850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31441 (p : Pattern) (selected : d301191 p = 1) : d305856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301186 q = 1) : d305851 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d301186, d305851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301186, d305851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31440 q selected
  have h2 (q : Pattern) (selected : d301187 q = 1) : d305852 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d301187, d305852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301187, d305852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301188 q = 1) : d305853 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d301188, d305853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301188, d305853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301189 q = 1) : d305854 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d301189, d305854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301189, d305854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301190 q = 1) : d305855 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d301190, d305855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301190, d305855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301191 q = 1) : d305856 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d301191, d305856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301191, d305856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31442 (p : Pattern) (selected : d301306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d562 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d564 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301306 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d301306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31443 (p : Pattern) (selected : d301309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1687 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301309 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d301309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro31444 (p : Pattern) (selected : d301318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301307 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31442 q selected
    | true =>
      simp only [d301307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301310 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31443 q selected
    | true =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301311 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301312 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301313 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301314 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d300722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31405 q selected
    | true =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d300723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d300974 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301315 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301316 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d301317 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d301317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d301318 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31445 (p : Pattern) (selected : d301323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31405 q selected
    | true =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300974 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300976 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31421 q selected
    | true =>
      simp only [d300976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300977 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d300977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d300978 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d300979 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d300980 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d300724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d300987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d300988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d300988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301323 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro31446 (p : Pattern) (selected : d301331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31405 q selected
    | true =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300974 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d300724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d300987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d300987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d300988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d300988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301331 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro31447 (p : Pattern) (selected : d301336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31405 q selected
    | true =>
      simp only [d300722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d300541 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d300725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d300726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d300726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301336 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro31448 (p : Pattern) (selected : d301342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301319 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31444 q selected
    | true =>
      simp only [d301319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301321 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301322 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301324 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31445 q selected
    | true =>
      simp only [d301324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301325 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301326 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301327 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301328 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31446 q selected
    | true =>
      simp only [d301332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d301337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
    | true =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301339 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301340 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d301341 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d301342 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31449 (p : Pattern) (selected : d301345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31422 q selected
    | true =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300984 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300985 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
    | true =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301339 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301340 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301343 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301344 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301345 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31450 (p : Pattern) (selected : d301349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
    | true =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301339 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301340 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301344 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301349 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31451 (p : Pattern) (selected : d301356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301346 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31448 q selected
    | true =>
      simp only [d301346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31449 q selected
  have h2 (q : Pattern) (selected : d301347 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301350 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31449 q selected
    | true =>
      simp only [d301350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31450 q selected
  have h5 (q : Pattern) (selected : d301351 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301352 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301353 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301354 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301355 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301356 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31452 (p : Pattern) (selected : d301360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301350 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31449 q selected
    | true =>
      simp only [d301350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31450 q selected
  have h2 (q : Pattern) (selected : d301351 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301352 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301354 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301359 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301360 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31453 (p : Pattern) (selected : d301366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301357 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31451 q selected
    | true =>
      simp only [d301357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301358 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301361 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31452 q selected
    | true =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301362 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301363 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301364 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301365 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31454 (p : Pattern) (selected : d301370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301361 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31452 q selected
    | true =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301362 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301370 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31455 (p : Pattern) (selected : d301382 p = 1) : d305863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301255 q = 1) : d301255 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301264 q = 1) : d301264 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301304 q = 1) : d301304 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d301371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31453 q selected
    | true =>
      simp only [d301371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31454 q selected
  have h5 (q : Pattern) (selected : d301372 q = 1) : d305859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301372, d305859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301372, d305859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301378 q = 1) : d301378 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d301379 q = 1) : d305860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301379, d305860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301379, d305860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301380 q = 1) : d305861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301380, d305861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301380, d305861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301381 q = 1) : d305862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301381, d305862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301381, d305862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301382 q = 1) : d305863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301382, d305863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301382, d305863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro31456 (p : Pattern) (selected : d301396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301357 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31451 q selected
    | true =>
      simp only [d301357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301358 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301361 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31452 q selected
    | true =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301362 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301363 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301364 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301365 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31457 (p : Pattern) (selected : d301397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301361 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31452 q selected
    | true =>
      simp only [d301361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301362 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301397 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31458 (p : Pattern) (selected : d301406 p = 1) : d305868 p = 1 := by
  have h0 (q : Pattern) (selected : d301255 q = 1) : d301255 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301264 q = 1) : d301264 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301304 q = 1) : d301304 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31453 q selected
    | true =>
      simp only [d301371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31454 q selected
  have h4 (q : Pattern) (selected : d301372 q = 1) : d305859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301372, d305859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301372, d305859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301378 q = 1) : d301378 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d301379 q = 1) : d305860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301379, d305860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301379, d305860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301380 q = 1) : d305861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301380, d305861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301380, d305861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301381 q = 1) : d305862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301381, d305862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301381, d305862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301388 q = 1) : d301388 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d301393 q = 1) : d301393 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d301395 q = 1) : d301395 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d301398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31456 q selected
    | true =>
      simp only [d301398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31457 q selected
  have h13 (q : Pattern) (selected : d301399 q = 1) : d305864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301399, d305864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301399, d305864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301402 q = 1) : d301402 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d301403 q = 1) : d305865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301403, d305865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301403, d305865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301404 q = 1) : d305866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301404, d305866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301404, d305866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301405 q = 1) : d305867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301405, d305867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301405, d305867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d301406 q = 1) : d305868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301406, d305868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301406, d305868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro31459 (p : Pattern) (selected : d301426 p = 1) : d305875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301395 q = 1) : d301395 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31456 q selected
    | true =>
      simp only [d301398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31457 q selected
  have h3 (q : Pattern) (selected : d301399 q = 1) : d305864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301399, d305864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301399, d305864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301402 q = 1) : d301402 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301403 q = 1) : d305865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301403, d305865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301403, d305865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301424 q = 1) : d305873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301424, d305873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301424, d305873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301425 q = 1) : d305874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301425, d305874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301425, d305874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301426 q = 1) : d305875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301426, d305875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301426, d305875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31460 (p : Pattern) (selected : d301514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31444 q selected
  have h2 (q : Pattern) (selected : d301319 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31444 q selected
    | true =>
      simp only [d301319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301320 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31445 q selected
  have h8 (q : Pattern) (selected : d301324 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31445 q selected
    | true =>
      simp only [d301324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301325 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31446 q selected
  have h15 (q : Pattern) (selected : d301332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31446 q selected
    | true =>
      simp only [d301332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d301507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d301508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d301508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d301509 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
  have h21 (q : Pattern) (selected : d301337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
    | true =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d301510 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d301510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d301338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d301511 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d301511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d301512 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d301512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d301513 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d301513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d301514 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro31461 (p : Pattern) (selected : d301517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31422 q selected
  have h2 (q : Pattern) (selected : d300982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31422 q selected
    | true =>
      simp only [d300982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301127 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301128 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301509 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
  have h8 (q : Pattern) (selected : d301337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
    | true =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301510 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301511 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301512 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301516 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301517 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31462 (p : Pattern) (selected : d301521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301509 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
  have h2 (q : Pattern) (selected : d301337 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31447 q selected
    | true =>
      simp only [d301337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301510 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301338 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301511 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301512 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301516 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301521 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31463 (p : Pattern) (selected : d301528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301518 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31460 q selected
    | true =>
      simp only [d301518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31461 q selected
  have h2 (q : Pattern) (selected : d301519 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301520 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31461 q selected
    | true =>
      simp only [d301522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31462 q selected
  have h5 (q : Pattern) (selected : d301523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301526 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301527 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301528 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31464 (p : Pattern) (selected : d301532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31461 q selected
    | true =>
      simp only [d301522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31462 q selected
  have h2 (q : Pattern) (selected : d301523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301526 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301531 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301532 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31465 (p : Pattern) (selected : d301538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301529 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31463 q selected
    | true =>
      simp only [d301529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301530 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31464 q selected
    | true =>
      simp only [d301533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301535 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301536 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301537 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301538 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31466 (p : Pattern) (selected : d301542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31464 q selected
    | true =>
      simp only [d301533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31467 (p : Pattern) (selected : d301554 p = 1) : d305885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301495 q = 1) : d301495 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31465 q selected
    | true =>
      simp only [d301543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31466 q selected
  have h3 (q : Pattern) (selected : d301544 q = 1) : d305881 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301544, d305881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301544, d305881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301550 q = 1) : d301550 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301551 q = 1) : d305882 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301551, d305882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301551, d305882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301552 q = 1) : d305883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301552, d305883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301552, d305883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301553 q = 1) : d305884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301553, d305884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301553, d305884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301554 q = 1) : d305885 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301554, d305885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301554, d305885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31468 (p : Pattern) (selected : d301571 p = 1) : d305891 p = 1 := by
  have h0 (q : Pattern) (selected : d301247 q = 1) : d301247 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301407 q = 1) : d305869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301407, d305869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31455 q selected
    | true =>
      simp only [d301407, d305869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31458 q selected
  have h2 (q : Pattern) (selected : d301420 q = 1) : d301420 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301421 q = 1) : d305870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301421, d305870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301421, d305870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301422 q = 1) : d305871 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301422, d305871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301422, d305871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301423 q = 1) : d305872 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301423, d305872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301423, d305872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301427 q = 1) : d305876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301427, d305876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301427, d305876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31459 q selected
  have h8 (q : Pattern) (selected : d301429 q = 1) : d301429 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d301430 q = 1) : d305877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301430, d305877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301430, d305877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301431 q = 1) : d305878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301431, d305878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301431, d305878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d301432 q = 1) : d305879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301432, d305879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301432, d305879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d301433 q = 1) : d305880 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d301433, d305880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301433, d305880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301555 q = 1) : d305886 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301555, d305886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301555, d305886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31467 q selected
  have h14 (q : Pattern) (selected : d301566 q = 1) : d301566 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d301567 q = 1) : d305887 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301567, d305887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301567, d305887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301568 q = 1) : d305888 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301568, d305888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301568, d305888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d301569 q = 1) : d305889 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301569, d305889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301569, d305889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d301570 q = 1) : d305890 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d301570, d305890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d301570, d305890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d301571 q = 1) : d305891 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d301571, d305891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301571, d305891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31469 (p : Pattern) (selected : d301577 p = 1) : d305897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301572 q = 1) : d305892 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d301572, d305892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301572, d305892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31468 q selected
  have h2 (q : Pattern) (selected : d301573 q = 1) : d305893 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d301573, d305893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301573, d305893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301574 q = 1) : d305894 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d301574, d305894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301574, d305894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301575 q = 1) : d305895 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d301575, d305895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301575, d305895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301576 q = 1) : d305896 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d301576, d305896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301576, d305896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301577 q = 1) : d305897 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d301577, d305897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301577, d305897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31470 (p : Pattern) (selected : d301716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301310 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31443 q selected
    | true =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301311 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301713 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301714 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301715 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301716 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro31471 (p : Pattern) (selected : d301721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1233 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301721 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d301721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro31472 (p : Pattern) (selected : d301727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301307 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31442 q selected
    | true =>
      simp only [d301307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301310 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31443 q selected
    | true =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301311 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301312 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301313 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301314 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31471 q selected
  have h12 (q : Pattern) (selected : d301723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h14 (q : Pattern) (selected : d301725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301727 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro31473 (p : Pattern) (selected : d301735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301733 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301734 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31471 q selected
  have h7 (q : Pattern) (selected : d301723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301310 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31443 q selected
    | true =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301311 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301725 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301726 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301735 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro31474 (p : Pattern) (selected : d301748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d301722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31471 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301310 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31443 q selected
    | true =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d301311 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d301724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301740 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d301741 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301742 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d301743 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
  have h10 (q : Pattern) (selected : d301744 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d301745 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h13 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h14 (q : Pattern) (selected : d300541 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h15 (q : Pattern) (selected : d301746 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301747 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h17 (q : Pattern) (selected : d301748 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro31475 (p : Pattern) (selected : d301754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301717 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31470 q selected
    | true =>
      simp only [d301717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301718 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301719 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301720 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31472 q selected
    | true =>
      simp only [d301728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31473 q selected
    | true =>
      simp only [d301736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301738 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301739 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d301749 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
    | true =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301751 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301752 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d301753 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d301754 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31476 (p : Pattern) (selected : d301755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d300972 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d300972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300973 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301307 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31442 q selected
    | true =>
      simp only [d301307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301310 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31443 q selected
    | true =>
      simp only [d301310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301311 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301312 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301313 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301314 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301722 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31420 q selected
    | true =>
      simp only [d301722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31471 q selected
  have h12 (q : Pattern) (selected : d301723 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301724 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h14 (q : Pattern) (selected : d301740 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301741 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301742 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d301755 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro31477 (p : Pattern) (selected : d301762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301756 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31476 q selected
    | true =>
      simp only [d301756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301757 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301758 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301759 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301749 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
    | true =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301751 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301752 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301760 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31478 (p : Pattern) (selected : d301766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301743 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d301743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
  have h2 (q : Pattern) (selected : d301744 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d301744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301745 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d301745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300539 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31390 q selected
    | true =>
      simp only [d300539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300540 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300541 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301746 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d301746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301747 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d301747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301766 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d301766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro31479 (p : Pattern) (selected : d301772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301749 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
    | true =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301751 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301752 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301767 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31478 q selected
    | true =>
      simp only [d301767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301768 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301769 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301770 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301771 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301772 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro31480 (p : Pattern) (selected : d301779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301763 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31475 q selected
    | true =>
      simp only [d301763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31477 q selected
  have h2 (q : Pattern) (selected : d301764 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301765 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301773 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31477 q selected
    | true =>
      simp only [d301773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31479 q selected
  have h5 (q : Pattern) (selected : d301774 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301775 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301776 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301777 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301778 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301779 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31481 (p : Pattern) (selected : d301783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301773 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31477 q selected
    | true =>
      simp only [d301773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31479 q selected
  have h2 (q : Pattern) (selected : d301774 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301775 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301777 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301782 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301783 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31482 (p : Pattern) (selected : d301789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301780 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31480 q selected
    | true =>
      simp only [d301780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301781 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31481 q selected
    | true =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301786 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301787 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301788 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301789 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31483 (p : Pattern) (selected : d301793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31481 q selected
    | true =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301793 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31484 (p : Pattern) (selected : d301821 p = 1) : d305905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301678 q = 1) : d301678 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301687 q = 1) : d301687 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301712 q = 1) : d301712 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d301794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31482 q selected
    | true =>
      simp only [d301794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31483 q selected
  have h5 (q : Pattern) (selected : d301795 q = 1) : d305901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301795, d305901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301795, d305901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301817 q = 1) : d301817 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d301818 q = 1) : d305902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301818, d305902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301818, d305902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301819 q = 1) : d305903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301819, d305903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301819, d305903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301820 q = 1) : d305904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301820, d305904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301820, d305904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301821 q = 1) : d305905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301821, d305905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301821, d305905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro31485 (p : Pattern) (selected : d301835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301780 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31480 q selected
    | true =>
      simp only [d301780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301781 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31481 q selected
    | true =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301786 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301787 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301788 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31486 (p : Pattern) (selected : d301836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31481 q selected
    | true =>
      simp only [d301784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301790 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301791 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301792 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31487 (p : Pattern) (selected : d301845 p = 1) : d305910 p = 1 := by
  have h0 (q : Pattern) (selected : d301678 q = 1) : d301678 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301687 q = 1) : d301687 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301712 q = 1) : d301712 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301794 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31482 q selected
    | true =>
      simp only [d301794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31483 q selected
  have h4 (q : Pattern) (selected : d301795 q = 1) : d305901 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301795, d305901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301795, d305901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301817 q = 1) : d301817 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d301818 q = 1) : d305902 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301818, d305902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301818, d305902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301819 q = 1) : d305903 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301819, d305903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301819, d305903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301820 q = 1) : d305904 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301820, d305904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301820, d305904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d301827 q = 1) : d301827 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d301832 q = 1) : d301832 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d301834 q = 1) : d301834 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d301837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31485 q selected
    | true =>
      simp only [d301837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31486 q selected
  have h13 (q : Pattern) (selected : d301838 q = 1) : d305906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301838, d305906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301838, d305906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301841 q = 1) : d301841 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d301842 q = 1) : d305907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301842, d305907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301842, d305907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d301843 q = 1) : d305908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301843, d305908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301843, d305908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301844 q = 1) : d305909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301844, d305909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301844, d305909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d301845 q = 1) : d305910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301845, d305910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301845, d305910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro31488 (p : Pattern) (selected : d301865 p = 1) : d305917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301834 q = 1) : d301834 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d301837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d301837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31485 q selected
    | true =>
      simp only [d301837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31486 q selected
  have h3 (q : Pattern) (selected : d301838 q = 1) : d305906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d301838, d305906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301838, d305906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301841 q = 1) : d301841 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301842 q = 1) : d305907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d301842, d305907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301842, d305907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301863 q = 1) : d305915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d301863, d305915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301863, d305915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301864 q = 1) : d305916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d301864, d305916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301864, d305916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301865 q = 1) : d305917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d301865, d305917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301865, d305917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31489 (p : Pattern) (selected : d301963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301945 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31470 q selected
  have h2 (q : Pattern) (selected : d301717 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31470 q selected
    | true =>
      simp only [d301717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301946 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301718 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301947 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301948 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301949 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31472 q selected
  have h8 (q : Pattern) (selected : d301728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31472 q selected
    | true =>
      simp only [d301728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301950 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301951 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301952 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301953 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301954 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31473 q selected
  have h15 (q : Pattern) (selected : d301736 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31473 q selected
    | true =>
      simp only [d301736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d301955 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d301955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d301737 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d301737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d301956 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d301956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d301957 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d301957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d301958 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
  have h21 (q : Pattern) (selected : d301749 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
    | true =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d301959 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d301959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d301750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d301960 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d301960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d301961 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d301961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d301962 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d301962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d301963 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro31490 (p : Pattern) (selected : d301970 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301964 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31476 q selected
  have h2 (q : Pattern) (selected : d301756 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31476 q selected
    | true =>
      simp only [d301756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301965 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301757 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301966 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301967 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301958 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
  have h8 (q : Pattern) (selected : d301749 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
    | true =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301959 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d301960 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d301961 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d301961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d301968 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d301969 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301970 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31491 (p : Pattern) (selected : d301979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301958 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
  have h2 (q : Pattern) (selected : d301749 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31474 q selected
    | true =>
      simp only [d301749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d301959 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301750 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301960 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301961 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301969 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301974 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31478 q selected
  have h9 (q : Pattern) (selected : d301767 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d301767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31478 q selected
    | true =>
      simp only [d301767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d301975 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d301975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d301768 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d301768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d301976 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d301976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d301977 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d301977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d301977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d301978 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d301978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d301978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d301979 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d301979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro31492 (p : Pattern) (selected : d301986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301971 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31489 q selected
    | true =>
      simp only [d301971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31490 q selected
  have h2 (q : Pattern) (selected : d301972 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301973 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301980 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31490 q selected
    | true =>
      simp only [d301980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31491 q selected
  have h5 (q : Pattern) (selected : d301981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301982 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301983 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d301984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d301985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro31493 (p : Pattern) (selected : d301990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301980 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d301980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31490 q selected
    | true =>
      simp only [d301980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31491 q selected
  have h2 (q : Pattern) (selected : d301981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d301981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301982 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d301982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d301984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d301984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301989 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d301989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d301990 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d301990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31494 (p : Pattern) (selected : d301996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31492 q selected
    | true =>
      simp only [d301987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31493 q selected
    | true =>
      simp only [d301991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d301993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d301994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d301995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d301996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d301996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro31495 (p : Pattern) (selected : d302000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d301991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31493 q selected
    | true =>
      simp only [d301991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d301992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d301992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d301997 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d301997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d301997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d301998 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d301999 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d301999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d302000 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d302000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d302000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro31496 (p : Pattern) (selected : d302027 p = 1) : d305927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301944 q = 1) : d301944 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d302001 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d302001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31494 q selected
    | true =>
      simp only [d302001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31495 q selected
  have h3 (q : Pattern) (selected : d302002 q = 1) : d305923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d302002, d305923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d302002, d305923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302023 q = 1) : d302023 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d302024 q = 1) : d305924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d302024, d305924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d302024, d305924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302025 q = 1) : d305925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d302025, d305925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302025, d305925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302026 q = 1) : d305926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d302026, d305926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302026, d305926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d302027 q = 1) : d305927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d302027, d305927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302027, d305927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro31497 (p : Pattern) (selected : d302044 p = 1) : d305933 p = 1 := by
  have h0 (q : Pattern) (selected : d301670 q = 1) : d301670 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d301846 q = 1) : d305911 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301846, d305911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31484 q selected
    | true =>
      simp only [d301846, d305911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31487 q selected
  have h2 (q : Pattern) (selected : d301859 q = 1) : d301859 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d301860 q = 1) : d305912 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301860, d305912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d301860, d305912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d301861 q = 1) : d305913 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301861, d305913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d301861, d305913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301862 q = 1) : d305914 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301862, d305914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301862, d305914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d301866 q = 1) : d305918 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d301866, d305918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d301866, d305918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31488 q selected
  have h8 (q : Pattern) (selected : d301868 q = 1) : d301868 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d301869 q = 1) : d305919 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d301869, d305919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d301869, d305919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d301870 q = 1) : d305920 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d301870, d305920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d301870, d305920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d301871 q = 1) : d305921 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d301871, d305921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d301871, d305921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d301872 q = 1) : d305922 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d301872, d305922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d301872, d305922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d302028 q = 1) : d305928 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d302028, d305928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302028, d305928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31496 q selected
  have h14 (q : Pattern) (selected : d302039 q = 1) : d302039 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d302040 q = 1) : d305929 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d302040, d305929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d302040, d305929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d302041 q = 1) : d305930 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d302041, d305930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d302041, d305930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d302042 q = 1) : d305931 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d302042, d305931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d302042, d305931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d302043 q = 1) : d305932 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d302043, d305932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d302043, d305932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d302044 q = 1) : d305933 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d302044, d305933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d302044, d305933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro31498 (p : Pattern) (selected : d302050 p = 1) : d305939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d302045 q = 1) : d305934 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d302045, d305934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302045, d305934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31497 q selected
  have h2 (q : Pattern) (selected : d302046 q = 1) : d305935 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d302046, d305935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302046, d305935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d302047 q = 1) : d305936 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d302047, d305936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302047, d305936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d302048 q = 1) : d305937 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d302048, d305937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302048, d305937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302049 q = 1) : d305938 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d302049, d305938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302049, d305938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d302050 q = 1) : d305939 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d302050, d305939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d302050, d305939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro31499 (p : Pattern) (selected : d302169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1691 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d302169 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d302169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d302169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
end NetHack.Soko22Hazard87
