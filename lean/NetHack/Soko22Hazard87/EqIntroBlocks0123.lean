import NetHack.Soko22Hazard87.EqIntroBlocks0122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro30750 (p : Pattern) (selected : d291443 p = 0) : d292758 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro492 q selected
    | true =>
      simp only [d1695, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro493 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1696 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro412 q selected
  have h3 (q : Pattern) (selected : d1697 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291442 q = 0) : d292757 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291442, d292757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291442, d292757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291443 q = 0) : d292758 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291443, d292758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291443, d292758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30751 (p : Pattern) (selected : d291449 p = 0) : d292764 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro496 q selected
    | true =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro497 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1715 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h3 (q : Pattern) (selected : d1716 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291448 q = 0) : d292763 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291448, d292763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291448, d292763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291449 q = 0) : d292764 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291449, d292764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291449, d292764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30752 (p : Pattern) (selected : d291456 p = 0) : d292771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1746 q = 0) : d53016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1746, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1746, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
  have h2 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h3 (q : Pattern) (selected : d1747 q = 0) : d53017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1747, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1747, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10249 q = 0) : d101556 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10249, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
    | true =>
      simp only [d10249, d101556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10250 q = 0) : d101557 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10250, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10250, d101557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291455 q = 0) : d292770 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291455, d292770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291455, d292770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291456 q = 0) : d292771 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291456, d292771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291456, d292771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30753 (p : Pattern) (selected : d291462 p = 0) : d292777 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291444 q = 0) : d292759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291444, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30750 q selected
    | true =>
      simp only [d291444, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291445 q = 0) : d292760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291445, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291445, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291446 q = 0) : d292761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291446, d292761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291446, d292761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291447 q = 0) : d292762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291447, d292762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291447, d292762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291450 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291450, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30751 q selected
    | true =>
      simp only [d291450, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291451 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291451, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291451, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291452 q = 0) : d292767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291452, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291452, d292767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291453 q = 0) : d292768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291453, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291453, d292768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291454 q = 0) : d292769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291454, d292769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291454, d292769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291457 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
    | true =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291458 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291459 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291459, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291459, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291460 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291460, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291460, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291461 q = 0) : d292776 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291461, d292776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291461, d292776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291462 q = 0) : d292777 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291462, d292777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291462, d292777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30754 (p : Pattern) (selected : d291464 p = 0) : d292779 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro496 q selected
    | true =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro497 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1715 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h3 (q : Pattern) (selected : d1716 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d26229 q = 0) : d199013 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d26229, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18891 q selected
    | true =>
      simp only [d26229, d199013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d26230 q = 0) : d199014 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d26230, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d26230, d199014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d291463 q = 0) : d292778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291463, d292778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291463, d292778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291464 q = 0) : d292779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291464, d292779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291464, d292779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro30755 (p : Pattern) (selected : d291471 p = 0) : d292786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291465 q = 0) : d292780 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291465, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30754 q selected
    | true =>
      simp only [d291465, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291466 q = 0) : d292781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291466, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291466, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291467 q = 0) : d292782 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291467, d292782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291467, d292782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291468 q = 0) : d292783 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291468, d292783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291468, d292783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291457 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
    | true =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291458 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291459 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291459, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291459, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291460 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291460, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291460, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291469 q = 0) : d292784 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291469, d292784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291469, d292784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291470 q = 0) : d292785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291470, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291470, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291471 q = 0) : d292786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291471, d292786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291471, d292786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30756 (p : Pattern) (selected : d291475 p = 0) : d292790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291457 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
    | true =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291458 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291459 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291459, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291459, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291460 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291460, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291460, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291470 q = 0) : d292785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291470, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291470, d292785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291475 q = 0) : d292790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291475, d292790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291475, d292790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30757 (p : Pattern) (selected : d291482 p = 0) : d292797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291472 q = 0) : d292787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291472, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30753 q selected
    | true =>
      simp only [d291472, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30755 q selected
  have h2 (q : Pattern) (selected : d291473 q = 0) : d292788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291473, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291473, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291474 q = 0) : d292789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291474, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291474, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291476 q = 0) : d292791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291476, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30755 q selected
    | true =>
      simp only [d291476, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30756 q selected
  have h5 (q : Pattern) (selected : d291477 q = 0) : d292792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291477, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291477, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291478 q = 0) : d292793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291478, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291478, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291479 q = 0) : d292794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291479, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291479, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291480 q = 0) : d292795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291480, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291480, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291481 q = 0) : d292796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291481, d292796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291481, d292796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291482 q = 0) : d292797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291482, d292797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291482, d292797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30758 (p : Pattern) (selected : d291486 p = 0) : d292801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291476 q = 0) : d292791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291476, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30755 q selected
    | true =>
      simp only [d291476, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30756 q selected
  have h2 (q : Pattern) (selected : d291477 q = 0) : d292792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291477, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291477, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291478 q = 0) : d292793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291478, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291478, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291480 q = 0) : d292795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291480, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291480, d292795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291485 q = 0) : d292800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291485, d292800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291485, d292800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291486 q = 0) : d292801 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291486, d292801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291486, d292801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30759 (p : Pattern) (selected : d291492 p = 0) : d292807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291483 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291483, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30757 q selected
    | true =>
      simp only [d291483, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291484 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291484, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291484, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291487 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30758 q selected
    | true =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291488 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291489 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291489, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291489, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291490 q = 0) : d292805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291490, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291490, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291491 q = 0) : d292806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291491, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291491, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291492 q = 0) : d292807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291492, d292807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291492, d292807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30760 (p : Pattern) (selected : d291496 p = 0) : d292811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291487 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30758 q selected
    | true =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291488 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291493 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291493, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291493, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291494 q = 0) : d292809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291494, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291494, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291495 q = 0) : d292810 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291495, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291495, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291496 q = 0) : d292811 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291496, d292811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291496, d292811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30761 (p : Pattern) (selected : d291500 p = 0) : d292875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5128 q = 0) : d69215 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
  have h2 (q : Pattern) (selected : d5129 q = 0) : d69216 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291499 q = 0) : d292874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291499, d292874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291499, d292874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291500 q = 0) : d292875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291500, d292875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291500, d292875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30762 (p : Pattern) (selected : d291506 p = 0) : d292881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291349 q = 0) : d292780 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30730 q selected
    | true =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291350 q = 0) : d292781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291351 q = 0) : d292782 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291351, d292782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291351, d292782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291352 q = 0) : d292783 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291352, d292783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291352, d292783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291343 q = 0) : d292774 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291343, d292774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291344 q = 0) : d292775 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291344, d292775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291353 q = 0) : d292784 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291353, d292784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291353, d292784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291501 q = 0) : d292876 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30761 q selected
    | true =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291502 q = 0) : d292877 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291503 q = 0) : d292878 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291503, d292878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291503, d292878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291504 q = 0) : d292879 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291504, d292879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291504, d292879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291505 q = 0) : d292880 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291505, d292880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291505, d292880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291506 q = 0) : d292881 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291506, d292881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291506, d292881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30763 (p : Pattern) (selected : d291507 p = 0) : d292882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291501 q = 0) : d292876 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30761 q selected
    | true =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291502 q = 0) : d292877 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291503 q = 0) : d292878 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291503, d292878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291503, d292878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291504 q = 0) : d292879 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291504, d292879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291504, d292879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291505 q = 0) : d292880 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291505, d292880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291505, d292880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291507 q = 0) : d292882 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291507, d292882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291507, d292882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30764 (p : Pattern) (selected : d291513 p = 0) : d292888 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291356 q = 0) : d292787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291356, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30729 q selected
    | true =>
      simp only [d291356, d292787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30731 q selected
  have h2 (q : Pattern) (selected : d291357 q = 0) : d292788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291357, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291357, d292788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291358 q = 0) : d292789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291358, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291358, d292789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291360 q = 0) : d292791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30731 q selected
    | true =>
      simp only [d291360, d292791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30732 q selected
  have h5 (q : Pattern) (selected : d291361 q = 0) : d292792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291361, d292792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291362 q = 0) : d292793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291362, d292793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291363 q = 0) : d292794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291363, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291363, d292794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291508 q = 0) : d292883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291508, d292883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30762 q selected
    | true =>
      simp only [d291508, d292883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30763 q selected
  have h9 (q : Pattern) (selected : d291509 q = 0) : d292884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291509, d292884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291509, d292884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291510 q = 0) : d292885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291510, d292885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291510, d292885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291511 q = 0) : d292886 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291511, d292886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291511, d292886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291512 q = 0) : d292887 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291512, d292887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291512, d292887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291513 q = 0) : d292888 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291513, d292888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291513, d292888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30765 (p : Pattern) (selected : d291519 p = 0) : d292894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291514 q = 0) : d292889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291514, d292889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30764 q selected
    | true =>
      simp only [d291514, d292889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291515 q = 0) : d292890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291515, d292890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291515, d292890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291516 q = 0) : d292891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291516, d292891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291516, d292891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291517 q = 0) : d292892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291517, d292892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291517, d292892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291518 q = 0) : d292893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291518, d292893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291518, d292893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291519 q = 0) : d292894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291519, d292894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291519, d292894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30766 (p : Pattern) (selected : d291525 p = 0) : d292900 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291404 q = 0) : d292835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291404, d292835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30741 q selected
    | true =>
      simp only [d291404, d292835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30742 q selected
  have h2 (q : Pattern) (selected : d291405 q = 0) : d292836 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291405, d292836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291405, d292836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291406 q = 0) : d292837 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291406, d292837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291406, d292837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291407 q = 0) : d292838 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291407, d292838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291407, d292838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291414 q = 0) : d292845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291414, d292845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30743 q selected
    | true =>
      simp only [d291414, d292845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30744 q selected
  have h6 (q : Pattern) (selected : d291415 q = 0) : d292846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291415, d292846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291415, d292846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291416 q = 0) : d292847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291416, d292847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291416, d292847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291441 q = 0) : d292872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291441, d292872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30749 q selected
    | true =>
      simp only [d291441, d292872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30735 q selected
  have h9 (q : Pattern) (selected : d291497 q = 0) : d292812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291497, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30759 q selected
    | true =>
      simp only [d291497, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30760 q selected
  have h10 (q : Pattern) (selected : d291498 q = 0) : d292873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291498, d292873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291498, d292873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291520 q = 0) : d292895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291520, d292895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30765 q selected
    | true =>
      simp only [d291520, d292895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291521 q = 0) : d292896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291521, d292896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291521, d292896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291522 q = 0) : d292897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291522, d292897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291522, d292897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291523 q = 0) : d292898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291523, d292898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291523, d292898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291524 q = 0) : d292899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291524, d292899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291524, d292899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291525 q = 0) : d292900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291525, d292900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291525, d292900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro30767 (p : Pattern) (selected : d291526 p = 0) : d292901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291373 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291374 q = 0) : d292805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291374, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291400 q = 0) : d292831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291400, d292831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291400, d292831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291526 q = 0) : d292901 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291526, d292901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291526, d292901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30768 (p : Pattern) (selected : d291527 p = 0) : d292902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291377 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291378 q = 0) : d292809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291378, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291402 q = 0) : d292833 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291402, d292833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291402, d292833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291527 q = 0) : d292902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291527, d292902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291527, d292902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30769 (p : Pattern) (selected : d291532 p = 0) : d292907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291373 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291373, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291408 q = 0) : d292839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291408, d292839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291408, d292839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291409 q = 0) : d292840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291409, d292840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291409, d292840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291532 q = 0) : d292907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291532, d292907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291532, d292907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30770 (p : Pattern) (selected : d291533 p = 0) : d292908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291371 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30734 q selected
    | true =>
      simp only [d291371, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291372 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291372, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291377 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291377, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291411 q = 0) : d292842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291411, d292842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291411, d292842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291412 q = 0) : d292843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291412, d292843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291412, d292843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291533 q = 0) : d292908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291533, d292908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291533, d292908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30771 (p : Pattern) (selected : d291537 p = 0) : d292912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291435 q = 0) : d292866 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291435, d292866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30748 q selected
    | true =>
      simp only [d291435, d292866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291436 q = 0) : d292867 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291436, d292867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291436, d292867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291367 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30733 q selected
    | true =>
      simp only [d291367, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291368 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291368, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291437 q = 0) : d292868 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291437, d292868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291437, d292868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291438 q = 0) : d292869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291438, d292869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291438, d292869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291439 q = 0) : d292870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291439, d292870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291439, d292870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291537 q = 0) : d292912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291537, d292912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291537, d292912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30772 (p : Pattern) (selected : d291539 p = 0) : d292820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291483 q = 0) : d292798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291483, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30757 q selected
    | true =>
      simp only [d291483, d292798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291484 q = 0) : d292799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291484, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291484, d292799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291487 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30758 q selected
    | true =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291488 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291489 q = 0) : d292804 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291489, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291489, d292804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291490 q = 0) : d292805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291490, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291490, d292805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291491 q = 0) : d292806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291491, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291491, d292806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291539 q = 0) : d292820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291539, d292820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291539, d292820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30773 (p : Pattern) (selected : d291540 p = 0) : d292821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291487 q = 0) : d292802 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30758 q selected
    | true =>
      simp only [d291487, d292802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291488 q = 0) : d292803 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, d292803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291493 q = 0) : d292808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291493, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291493, d292808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291494 q = 0) : d292809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291494, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291494, d292809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291495 q = 0) : d292810 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291495, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291495, d292810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291540 q = 0) : d292821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291540, d292821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291540, d292821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30774 (p : Pattern) (selected : d291543 p = 0) : d292915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291514 q = 0) : d292889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291514, d292889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30764 q selected
    | true =>
      simp only [d291514, d292889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291515 q = 0) : d292890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291515, d292890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291515, d292890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291516 q = 0) : d292891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291516, d292891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291516, d292891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291517 q = 0) : d292892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291517, d292892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291517, d292892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291518 q = 0) : d292893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291518, d292893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291518, d292893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291543 q = 0) : d292915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291543, d292915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291543, d292915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30775 (p : Pattern) (selected : d291549 p = 0) : d292921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291404 q = 0) : d292835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291404, d292835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30741 q selected
    | true =>
      simp only [d291404, d292835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30742 q selected
  have h2 (q : Pattern) (selected : d291405 q = 0) : d292836 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291405, d292836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291405, d292836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291406 q = 0) : d292837 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291406, d292837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291406, d292837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291407 q = 0) : d292838 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291407, d292838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291407, d292838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291414 q = 0) : d292845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291414, d292845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30743 q selected
    | true =>
      simp only [d291414, d292845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30744 q selected
  have h6 (q : Pattern) (selected : d291415 q = 0) : d292846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291415, d292846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291415, d292846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291416 q = 0) : d292847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291416, d292847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291416, d292847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291441 q = 0) : d292872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291441, d292872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30749 q selected
    | true =>
      simp only [d291441, d292872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30735 q selected
  have h9 (q : Pattern) (selected : d291497 q = 0) : d292812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291497, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30759 q selected
    | true =>
      simp only [d291497, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30760 q selected
  have h10 (q : Pattern) (selected : d291498 q = 0) : d292873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291498, d292873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291498, d292873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291520 q = 0) : d292895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291520, d292895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30765 q selected
    | true =>
      simp only [d291520, d292895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291521 q = 0) : d292896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291521, d292896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291521, d292896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291522 q = 0) : d292897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291522, d292897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291522, d292897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291523 q = 0) : d292898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291523, d292898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291523, d292898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291524 q = 0) : d292899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291524, d292899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291524, d292899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291528 q = 0) : d292903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291528, d292903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30767 q selected
    | true =>
      simp only [d291528, d292903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30768 q selected
  have h17 (q : Pattern) (selected : d291529 q = 0) : d292904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291529, d292904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291529, d292904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d291530 q = 0) : d292905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291530, d292905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d291530, d292905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d291531 q = 0) : d292906 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291531, d292906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291531, d292906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d291534 q = 0) : d292909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291534, d292909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30769 q selected
    | true =>
      simp only [d291534, d292909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30770 q selected
  have h21 (q : Pattern) (selected : d291535 q = 0) : d292910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291535, d292910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291535, d292910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d291536 q = 0) : d292911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291536, d292911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d291536, d292911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d291538 q = 0) : d292913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291538, d292913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30771 q selected
    | true =>
      simp only [d291538, d292913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30738 q selected
  have h24 (q : Pattern) (selected : d291541 q = 0) : d292822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291541, d292822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30772 q selected
    | true =>
      simp only [d291541, d292822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30773 q selected
  have h25 (q : Pattern) (selected : d291542 q = 0) : d292914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291542, d292914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d291542, d292914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d291544 q = 0) : d292916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291544, d292916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30774 q selected
    | true =>
      simp only [d291544, d292916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d291545 q = 0) : d292917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291545, d292917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d291545, d292917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d291546 q = 0) : d292918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291546, d292918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d291546, d292918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d291547 q = 0) : d292919 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291547, d292919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d291547, d292919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d291548 q = 0) : d292920 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291548, d292920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d291548, d292920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d291549 q = 0) : d292921 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291549, d292921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291549, d292921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro30776 (p : Pattern) (selected : d291556 p = 0) : d292928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291381 q = 0) : d292812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291381, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30735 q selected
    | true =>
      simp only [d291381, d292812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30736 q selected
  have h2 (q : Pattern) (selected : d291382 q = 0) : d292813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291382, d292813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291382, d292813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291383 q = 0) : d292814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291383, d292814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291383, d292814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291384 q = 0) : d292815 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291384, d292815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291384, d292815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291385 q = 0) : d292816 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291385, d292816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291385, d292816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291551 q = 0) : d292923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291551, d292923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30736 q selected
    | true =>
      simp only [d291551, d292923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291552 q = 0) : d292924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291552, d292924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291552, d292924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291553 q = 0) : d292925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291553, d292925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291553, d292925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291554 q = 0) : d292926 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291554, d292926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291554, d292926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291555 q = 0) : d292927 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291555, d292927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291555, d292927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291556 q = 0) : d292928 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291556, d292928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291556, d292928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30777 (p : Pattern) (selected : d291562 p = 0) : d292934 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291551 q = 0) : d292923 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291551, d292923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30736 q selected
    | true =>
      simp only [d291551, d292923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291552 q = 0) : d292924 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291552, d292924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291552, d292924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291553 q = 0) : d292925 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291553, d292925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291553, d292925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291554 q = 0) : d292926 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291554, d292926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291554, d292926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291555 q = 0) : d292927 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291555, d292927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291555, d292927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291557 q = 0) : d292929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291557, d292929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30739 q selected
    | true =>
      simp only [d291557, d292929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291558 q = 0) : d292930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291558, d292930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291558, d292930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291559 q = 0) : d292931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291559, d292931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291559, d292931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291560 q = 0) : d292932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291560, d292932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291560, d292932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291561 q = 0) : d292933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291561, d292933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291561, d292933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291562 q = 0) : d292934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291562, d292934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291562, d292934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30778 (p : Pattern) (selected : d291569 p = 0) : d292941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291538 q = 0) : d292913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291538, d292913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30771 q selected
    | true =>
      simp only [d291538, d292913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30738 q selected
  have h2 (q : Pattern) (selected : d291541 q = 0) : d292822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291541, d292822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30772 q selected
    | true =>
      simp only [d291541, d292822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30773 q selected
  have h3 (q : Pattern) (selected : d291542 q = 0) : d292914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291542, d292914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291542, d292914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291544 q = 0) : d292916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291544, d292916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30774 q selected
    | true =>
      simp only [d291544, d292916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291545 q = 0) : d292917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291545, d292917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291545, d292917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291546 q = 0) : d292918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291546, d292918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291546, d292918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291567 q = 0) : d292939 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291567, d292939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291567, d292939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291568 q = 0) : d292940 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291568, d292940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291568, d292940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291569 q = 0) : d292941 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291569, d292941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291569, d292941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30779 (p : Pattern) (selected : d291571 p = 0) : d292943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291557 q = 0) : d292929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291557, d292929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30739 q selected
    | true =>
      simp only [d291557, d292929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291558 q = 0) : d292930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291558, d292930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291558, d292930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291559 q = 0) : d292931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291559, d292931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291559, d292931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291560 q = 0) : d292932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291560, d292932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291560, d292932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291561 q = 0) : d292933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291561, d292933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291561, d292933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291571 q = 0) : d292943 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291571, d292943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291571, d292943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30780 (p : Pattern) (selected : d291591 p = 0) : d292963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291577 q = 0) : d292949 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291577, d292949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291577, d292949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30745 q selected
  have h2 (q : Pattern) (selected : d291419 q = 0) : d292850 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291419, d292850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30745 q selected
    | true =>
      simp only [d291419, d292850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291578 q = 0) : d292950 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291578, d292950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291578, d292950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291420 q = 0) : d292851 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291420, d292851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291420, d292851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291579 q = 0) : d292951 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291579, d292951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291579, d292951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291580 q = 0) : d292952 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291580, d292952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291580, d292952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291581 q = 0) : d292953 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291581, d292953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291581, d292953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30726 q selected
  have h8 (q : Pattern) (selected : d291328 q = 0) : d292759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30726 q selected
    | true =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291582 q = 0) : d292954 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291582, d292954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291582, d292954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291329 q = 0) : d292760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291583 q = 0) : d292955 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291583, d292955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291583, d292955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291584 q = 0) : d292956 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291584, d292956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291584, d292956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291585 q = 0) : d292957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291585, d292957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291585, d292957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291586 q = 0) : d292958 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291586, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291586, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
  have h15 (q : Pattern) (selected : d291334 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
    | true =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291587 q = 0) : d292959 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291587, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291587, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291335 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291588 q = 0) : d292960 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291588, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291588, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291589 q = 0) : d292961 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291589, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291589, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291590 q = 0) : d292962 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291590, d292962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291590, d292962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291591 q = 0) : d292963 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291591, d292963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291591, d292963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30781 (p : Pattern) (selected : d291597 p = 0) : d292969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291581 q = 0) : d292953 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291581, d292953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291581, d292953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30726 q selected
  have h2 (q : Pattern) (selected : d291328 q = 0) : d292759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30726 q selected
    | true =>
      simp only [d291328, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291582 q = 0) : d292954 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291582, d292954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291582, d292954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291329 q = 0) : d292760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291329, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291583 q = 0) : d292955 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291583, d292955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291583, d292955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291584 q = 0) : d292956 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291584, d292956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291584, d292956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291586 q = 0) : d292958 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291586, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291586, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
  have h8 (q : Pattern) (selected : d291334 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
    | true =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291587 q = 0) : d292959 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291587, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291587, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291335 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291588 q = 0) : d292960 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291588, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291588, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291589 q = 0) : d292961 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291589, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291589, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291590 q = 0) : d292962 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291590, d292962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291590, d292962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291592 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
  have h15 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291593 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291594 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291595 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291596 q = 0) : d292968 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291596, d292968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291596, d292968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291597 q = 0) : d292969 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291597, d292969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291597, d292969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30782 (p : Pattern) (selected : d291602 p = 0) : d292974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291586 q = 0) : d292958 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291586, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291586, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
  have h2 (q : Pattern) (selected : d291334 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30727 q selected
    | true =>
      simp only [d291334, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291587 q = 0) : d292959 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291587, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291587, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291335 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291335, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291588 q = 0) : d292960 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291588, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291588, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291589 q = 0) : d292961 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291589, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291589, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291592 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
  have h8 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291593 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291594 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291595 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291596 q = 0) : d292968 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291596, d292968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291596, d292968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291601 q = 0) : d292973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291601, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291601, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291602 q = 0) : d292974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291602, d292974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291602, d292974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30783 (p : Pattern) (selected : d291612 p = 0) : d292984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291607 q = 0) : d292979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291607, d292979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291607, d292979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30730 q selected
  have h2 (q : Pattern) (selected : d291349 q = 0) : d292780 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30730 q selected
    | true =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291608 q = 0) : d292980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291608, d292980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291608, d292980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291350 q = 0) : d292781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291609 q = 0) : d292981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291609, d292981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291609, d292981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291610 q = 0) : d292982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291610, d292982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291610, d292982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291592 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
  have h8 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291593 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291594 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291595 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291611 q = 0) : d292983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291611, d292983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291611, d292983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291601 q = 0) : d292973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291601, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291601, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291612 q = 0) : d292984 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291612, d292984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291612, d292984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30784 (p : Pattern) (selected : d291616 p = 0) : d292988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291592 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
  have h2 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291593 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291594 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291595 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291601 q = 0) : d292973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291601, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291601, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291616 q = 0) : d292988 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291616, d292988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291616, d292988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30785 (p : Pattern) (selected : d291622 p = 0) : d292994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291598 q = 0) : d292970 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291598, d292970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30780 q selected
    | true =>
      simp only [d291598, d292970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30781 q selected
  have h2 (q : Pattern) (selected : d291599 q = 0) : d292971 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291599, d292971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291599, d292971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291600 q = 0) : d292972 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291600, d292972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291600, d292972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291603 q = 0) : d292975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291603, d292975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30781 q selected
    | true =>
      simp only [d291603, d292975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30782 q selected
  have h5 (q : Pattern) (selected : d291604 q = 0) : d292976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291604, d292976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291604, d292976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291605 q = 0) : d292977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291605, d292977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291605, d292977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291606 q = 0) : d292978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291606, d292978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291606, d292978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291613 q = 0) : d292985 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291613, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30781 q selected
    | true =>
      simp only [d291613, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30783 q selected
  have h9 (q : Pattern) (selected : d291614 q = 0) : d292986 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291614, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291614, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291615 q = 0) : d292987 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291615, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291615, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291617 q = 0) : d292989 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30783 q selected
    | true =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30784 q selected
  have h12 (q : Pattern) (selected : d291618 q = 0) : d292990 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291619 q = 0) : d292991 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291620 q = 0) : d292992 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291620, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291620, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291621 q = 0) : d292993 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291621, d292993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291621, d292993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291622 q = 0) : d292994 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291622, d292994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291622, d292994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro30786 (p : Pattern) (selected : d291627 p = 0) : d292999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291613 q = 0) : d292985 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291613, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30781 q selected
    | true =>
      simp only [d291613, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30783 q selected
  have h2 (q : Pattern) (selected : d291614 q = 0) : d292986 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291614, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291614, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291615 q = 0) : d292987 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291615, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291615, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291617 q = 0) : d292989 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30783 q selected
    | true =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30784 q selected
  have h5 (q : Pattern) (selected : d291618 q = 0) : d292990 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291619 q = 0) : d292991 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291620 q = 0) : d292992 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291620, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291620, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291625 q = 0) : d292997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291625, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291625, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291626 q = 0) : d292998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291626, d292998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291626, d292998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291627 q = 0) : d292999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291627, d292999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291627, d292999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30787 (p : Pattern) (selected : d291633 p = 0) : d293005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291623 q = 0) : d292995 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291623, d292995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30785 q selected
    | true =>
      simp only [d291623, d292995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291624 q = 0) : d292996 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291624, d292996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291624, d292996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291628 q = 0) : d293000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291628, d293000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30786 q selected
    | true =>
      simp only [d291628, d293000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291629 q = 0) : d293001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291629, d293001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291629, d293001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291630 q = 0) : d293002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291630, d293002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291630, d293002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291631 q = 0) : d293003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291631, d293003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291631, d293003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291632 q = 0) : d293004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291632, d293004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291632, d293004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291633 q = 0) : d293005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291633, d293005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291633, d293005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30788 (p : Pattern) (selected : d291635 p = 0) : d293007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291617 q = 0) : d292989 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30783 q selected
    | true =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30784 q selected
  have h2 (q : Pattern) (selected : d291618 q = 0) : d292990 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291619 q = 0) : d292991 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291625 q = 0) : d292997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291625, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291625, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291634 q = 0) : d293006 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291634, d293006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291634, d293006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291635 q = 0) : d293007 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291635, d293007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291635, d293007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30789 (p : Pattern) (selected : d291641 p = 0) : d293013 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291628 q = 0) : d293000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291628, d293000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30786 q selected
    | true =>
      simp only [d291628, d293000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291629 q = 0) : d293001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291629, d293001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291629, d293001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291636 q = 0) : d293008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291636, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30788 q selected
    | true =>
      simp only [d291636, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291637 q = 0) : d293009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291637, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291637, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291638 q = 0) : d293010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291638, d293010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291638, d293010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291639 q = 0) : d293011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291639, d293011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291639, d293011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291640 q = 0) : d293012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291640, d293012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291640, d293012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291641 q = 0) : d293013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291641, d293013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291641, d293013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30790 (p : Pattern) (selected : d291657 p = 0) : d292969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291643 q = 0) : d292953 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291643, d292953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291643, d292953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30750 q selected
  have h2 (q : Pattern) (selected : d291444 q = 0) : d292759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291444, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30750 q selected
    | true =>
      simp only [d291444, d292759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291644 q = 0) : d292954 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291644, d292954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291644, d292954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291445 q = 0) : d292760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291445, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291445, d292760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291645 q = 0) : d292955 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291645, d292955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291645, d292955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291646 q = 0) : d292956 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291646, d292956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291646, d292956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291647 q = 0) : d292958 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291647, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291647, d292958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30751 q selected
  have h8 (q : Pattern) (selected : d291450 q = 0) : d292765 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291450, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30751 q selected
    | true =>
      simp only [d291450, d292765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291648 q = 0) : d292959 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291648, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291648, d292959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291451 q = 0) : d292766 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291451, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291451, d292766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291649 q = 0) : d292960 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291649, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291649, d292960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291650 q = 0) : d292961 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291650, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291650, d292961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291651 q = 0) : d292962 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291651, d292962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291651, d292962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291652 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291652, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291652, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
  have h15 (q : Pattern) (selected : d291457 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
    | true =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291653 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291653, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291653, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291458 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291654 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291654, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291654, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291655 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291655, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291655, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291656 q = 0) : d292968 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291656, d292968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291656, d292968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291657 q = 0) : d292969 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291657, d292969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291657, d292969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30791 (p : Pattern) (selected : d291664 p = 0) : d292984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291658 q = 0) : d292979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291658, d292979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291658, d292979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30754 q selected
  have h2 (q : Pattern) (selected : d291465 q = 0) : d292780 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291465, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30754 q selected
    | true =>
      simp only [d291465, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291659 q = 0) : d292980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291659, d292980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291659, d292980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291466 q = 0) : d292781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291466, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291466, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291660 q = 0) : d292981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291660, d292981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291660, d292981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291661 q = 0) : d292982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291661, d292982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291661, d292982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291652 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291652, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291652, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
  have h8 (q : Pattern) (selected : d291457 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
    | true =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291653 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291653, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291653, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291458 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291654 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291654, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291654, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291655 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291655, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291655, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291662 q = 0) : d292983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291662, d292983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291662, d292983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291663 q = 0) : d292973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291663, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291663, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291664 q = 0) : d292984 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291664, d292984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291664, d292984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30792 (p : Pattern) (selected : d291668 p = 0) : d292988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291652 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291652, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291652, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
  have h2 (q : Pattern) (selected : d291457 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30752 q selected
    | true =>
      simp only [d291457, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291653 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291653, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291653, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291458 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291458, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291654 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291654, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291654, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291655 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291655, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291655, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291663 q = 0) : d292973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291663, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291663, d292973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291668 q = 0) : d292988 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291668, d292988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291668, d292988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30793 (p : Pattern) (selected : d291675 p = 0) : d292999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291665 q = 0) : d292985 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291665, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30790 q selected
    | true =>
      simp only [d291665, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30791 q selected
  have h2 (q : Pattern) (selected : d291666 q = 0) : d292986 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291666, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291666, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291667 q = 0) : d292987 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291667, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291667, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291669 q = 0) : d292989 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291669, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30791 q selected
    | true =>
      simp only [d291669, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30792 q selected
  have h5 (q : Pattern) (selected : d291670 q = 0) : d292990 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291670, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291670, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291671 q = 0) : d292991 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291671, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291671, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291672 q = 0) : d292992 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291672, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291672, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291673 q = 0) : d292997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291673, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291673, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291674 q = 0) : d292998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291674, d292998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291674, d292998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291675 q = 0) : d292999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291675, d292999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291675, d292999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30794 (p : Pattern) (selected : d291679 p = 0) : d293007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291669 q = 0) : d292989 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291669, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30791 q selected
    | true =>
      simp only [d291669, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30792 q selected
  have h2 (q : Pattern) (selected : d291670 q = 0) : d292990 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291670, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291670, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291671 q = 0) : d292991 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291671, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291671, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291673 q = 0) : d292997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291673, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291673, d292997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291678 q = 0) : d293006 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291678, d293006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291678, d293006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291679 q = 0) : d293007 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291679, d293007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291679, d293007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30795 (p : Pattern) (selected : d291685 p = 0) : d293013 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291676 q = 0) : d293000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291676, d293000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30793 q selected
    | true =>
      simp only [d291676, d293000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291677 q = 0) : d293001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291677, d293001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291677, d293001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291680 q = 0) : d293008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291680, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30794 q selected
    | true =>
      simp only [d291680, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291681 q = 0) : d293009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291681, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291681, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291682 q = 0) : d293010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291682, d293010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291682, d293010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291683 q = 0) : d293011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291683, d293011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291683, d293011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291684 q = 0) : d293012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291684, d293012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291684, d293012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291685 q = 0) : d293013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291685, d293013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291685, d293013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30796 (p : Pattern) (selected : d291689 p = 0) : d293018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291680 q = 0) : d293008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291680, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30794 q selected
    | true =>
      simp only [d291680, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291681 q = 0) : d293009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291681, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291681, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291686 q = 0) : d293015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291686, d293015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291686, d293015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291687 q = 0) : d293016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291687, d293016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291687, d293016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291688 q = 0) : d293017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291688, d293017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291688, d293017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291689 q = 0) : d293018 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291689, d293018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291689, d293018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30797 (p : Pattern) (selected : d291697 p = 0) : d293026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291607 q = 0) : d292979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291607, d292979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291607, d292979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30730 q selected
  have h2 (q : Pattern) (selected : d291349 q = 0) : d292780 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30730 q selected
    | true =>
      simp only [d291349, d292780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291608 q = 0) : d292980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291608, d292980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291608, d292980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291350 q = 0) : d292781 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291350, d292781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291609 q = 0) : d292981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291609, d292981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291609, d292981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291610 q = 0) : d292982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291610, d292982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291610, d292982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291592 q = 0) : d292964 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291592, d292964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
  have h8 (q : Pattern) (selected : d291341 q = 0) : d292772 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30728 q selected
    | true =>
      simp only [d291341, d292772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291593 q = 0) : d292965 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291593, d292965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291342 q = 0) : d292773 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291342, d292773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291594 q = 0) : d292966 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291594, d292966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291595 q = 0) : d292967 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291595, d292967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291611 q = 0) : d292983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291611, d292983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291611, d292983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291692 q = 0) : d293021 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291692, d293021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291692, d293021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30761 q selected
  have h15 (q : Pattern) (selected : d291501 q = 0) : d292876 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30761 q selected
    | true =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291693 q = 0) : d293022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291693, d293022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291693, d293022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291502 q = 0) : d292877 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291694 q = 0) : d293023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291694, d293023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291694, d293023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291695 q = 0) : d293024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291695, d293024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291695, d293024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291696 q = 0) : d293025 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291696, d293025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d291696, d293025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d291697 q = 0) : d293026 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291697, d293026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291697, d293026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30798 (p : Pattern) (selected : d291698 p = 0) : d293027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291692 q = 0) : d293021 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291692, d293021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291692, d293021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30761 q selected
  have h2 (q : Pattern) (selected : d291501 q = 0) : d292876 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30761 q selected
    | true =>
      simp only [d291501, d292876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291693 q = 0) : d293022 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291693, d293022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291693, d293022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291502 q = 0) : d292877 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291502, d292877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291694 q = 0) : d293023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291694, d293023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291694, d293023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291695 q = 0) : d293024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291695, d293024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291695, d293024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291696 q = 0) : d293025 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291696, d293025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291696, d293025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291698 q = 0) : d293027 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291698, d293027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291698, d293027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30799 (p : Pattern) (selected : d291704 p = 0) : d293033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291613 q = 0) : d292985 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291613, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30781 q selected
    | true =>
      simp only [d291613, d292985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30783 q selected
  have h2 (q : Pattern) (selected : d291614 q = 0) : d292986 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291614, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291614, d292986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291615 q = 0) : d292987 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291615, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291615, d292987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291617 q = 0) : d292989 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30783 q selected
    | true =>
      simp only [d291617, d292989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30784 q selected
  have h5 (q : Pattern) (selected : d291618 q = 0) : d292990 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291618, d292990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291619 q = 0) : d292991 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291619, d292991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291620 q = 0) : d292992 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291620, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291620, d292992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291699 q = 0) : d293028 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291699, d293028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30797 q selected
    | true =>
      simp only [d291699, d293028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30798 q selected
  have h9 (q : Pattern) (selected : d291700 q = 0) : d293029 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291700, d293029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291700, d293029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291701 q = 0) : d293030 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291701, d293030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291701, d293030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291702 q = 0) : d293031 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291702, d293031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291702, d293031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291703 q = 0) : d293032 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291703, d293032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291703, d293032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291704 q = 0) : d293033 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291704, d293033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291704, d293033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30800 (p : Pattern) (selected : d291710 p = 0) : d293039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291705 q = 0) : d293034 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291705, d293034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30799 q selected
    | true =>
      simp only [d291705, d293034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291706 q = 0) : d293035 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291706, d293035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291706, d293035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291707 q = 0) : d293036 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291707, d293036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291707, d293036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291708 q = 0) : d293037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291708, d293037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291708, d293037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291709 q = 0) : d293038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291709, d293038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291709, d293038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291710 q = 0) : d293039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291710, d293039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291710, d293039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30801 (p : Pattern) (selected : d291716 p = 0) : d293045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291642 q = 0) : d293014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291642, d293014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30787 q selected
    | true =>
      simp only [d291642, d293014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30789 q selected
  have h2 (q : Pattern) (selected : d291690 q = 0) : d293019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291690, d293019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30795 q selected
    | true =>
      simp only [d291690, d293019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30796 q selected
  have h3 (q : Pattern) (selected : d291691 q = 0) : d293020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291691, d293020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291691, d293020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291711 q = 0) : d293040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291711, d293040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30800 q selected
    | true =>
      simp only [d291711, d293040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291712 q = 0) : d293041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291712, d293041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291712, d293041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291713 q = 0) : d293042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291713, d293042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291713, d293042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291714 q = 0) : d293043 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291714, d293043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291714, d293043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291715 q = 0) : d293044 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291715, d293044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291715, d293044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291716 q = 0) : d293045 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291716, d293045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291716, d293045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30802 (p : Pattern) (selected : d291721 p = 0) : d293018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291636 q = 0) : d293008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291636, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30788 q selected
    | true =>
      simp only [d291636, d293008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291637 q = 0) : d293009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291637, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291637, d293009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291718 q = 0) : d293015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291718, d293015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291718, d293015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291719 q = 0) : d293016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291719, d293016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291719, d293016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291720 q = 0) : d293017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291720, d293017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291720, d293017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291721 q = 0) : d293018 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291721, d293018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291721, d293018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30803 (p : Pattern) (selected : d291727 p = 0) : d293052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291722 q = 0) : d293047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291722, d293047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30802 q selected
    | true =>
      simp only [d291722, d293047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291723 q = 0) : d293048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291723, d293048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291723, d293048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291724 q = 0) : d293049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291724, d293049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291724, d293049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291725 q = 0) : d293050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291725, d293050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291725, d293050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291726 q = 0) : d293051 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291726, d293051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291726, d293051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291727 q = 0) : d293052 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291727, d293052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291727, d293052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30804 (p : Pattern) (selected : d291733 p = 0) : d293058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291387 q = 0) : d292818 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291387, d292818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291387, d292818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30737 q selected
  have h2 (q : Pattern) (selected : d291388 q = 0) : d292819 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291388, d292819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291388, d292819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291397 q = 0) : d292828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291397, d292828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30737 q selected
    | true =>
      simp only [d291397, d292828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30740 q selected
  have h4 (q : Pattern) (selected : d291398 q = 0) : d292829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291398, d292829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291398, d292829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291399 q = 0) : d292830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291399, d292830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291399, d292830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291550 q = 0) : d292922 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291550, d292922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30766 q selected
    | true =>
      simp only [d291550, d292922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30775 q selected
  have h7 (q : Pattern) (selected : d291563 q = 0) : d292935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291563, d292935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30776 q selected
    | true =>
      simp only [d291563, d292935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30777 q selected
  have h8 (q : Pattern) (selected : d291564 q = 0) : d292936 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291564, d292936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291564, d292936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291565 q = 0) : d292937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291565, d292937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291565, d292937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d291566 q = 0) : d292938 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291566, d292938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291566, d292938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291570 q = 0) : d292942 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291570, d292942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291570, d292942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30778 q selected
  have h12 (q : Pattern) (selected : d291572 q = 0) : d292944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291572, d292944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291572, d292944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30779 q selected
  have h13 (q : Pattern) (selected : d291573 q = 0) : d292945 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291573, d292945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291573, d292945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291574 q = 0) : d292946 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291574, d292946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291574, d292946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291575 q = 0) : d292947 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291575, d292947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291575, d292947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291576 q = 0) : d292948 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291576, d292948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291576, d292948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291717 q = 0) : d293046 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291717, d293046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291717, d293046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30801 q selected
  have h18 (q : Pattern) (selected : d291728 q = 0) : d293053 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291728, d293053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291728, d293053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30803 q selected
  have h19 (q : Pattern) (selected : d291729 q = 0) : d293054 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291729, d293054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d291729, d293054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d291730 q = 0) : d293055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291730, d293055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d291730, d293055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d291731 q = 0) : d293056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291731, d293056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d291731, d293056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d291732 q = 0) : d293057 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291732, d293057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d291732, d293057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d291733 q = 0) : d293058 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d291733, d293058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291733, d293058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro30805 (p : Pattern) (selected : d291739 p = 0) : d293064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291734 q = 0) : d293059 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d291734, d293059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291734, d293059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30804 q selected
  have h2 (q : Pattern) (selected : d291735 q = 0) : d293060 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d291735, d293060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291735, d293060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291736 q = 0) : d293061 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d291736, d293061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291736, d293061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291737 q = 0) : d293062 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d291737, d293062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291737, d293062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291738 q = 0) : d293063 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d291738, d293063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291738, d293063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291739 q = 0) : d293064 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d291739, d293064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291739, d293064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30806 (p : Pattern) (selected : d291745 p = 0) : d293070 p = 1 := by
  have h0 (q : Pattern) (selected : d2020 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro549 q selected
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro550 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2024 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro551 q selected
  have h3 (q : Pattern) (selected : d2025 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291744 q = 0) : d293069 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291744, d293069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291744, d293069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291745 q = 0) : d293070 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291745, d293070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291745, d293070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30807 (p : Pattern) (selected : d291752 p = 0) : d293077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2058 q = 0) : d53337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
  have h2 (q : Pattern) (selected : d2043 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h3 (q : Pattern) (selected : d2059 q = 0) : d53338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10405 q = 0) : d101726 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10406 q = 0) : d101727 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10407 q = 0) : d101728 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291751 q = 0) : d293076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291751, d293076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291751, d293076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291752 q = 0) : d293077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291752, d293077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291752, d293077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30808 (p : Pattern) (selected : d291758 p = 0) : d293083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154503 q = 0) : d156196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154504 q = 0) : d156197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291748 q = 0) : d293073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291749 q = 0) : d293074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291750 q = 0) : d293075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291750, d293075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291750, d293075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291755 q = 0) : d293080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291756 q = 0) : d293081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291757 q = 0) : d293082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291757, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291757, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291758 q = 0) : d293083 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291758, d293083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291758, d293083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30809 (p : Pattern) (selected : d291760 p = 0) : d293085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291748 q = 0) : d293073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291749 q = 0) : d293074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291755 q = 0) : d293080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291756 q = 0) : d293081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291757 q = 0) : d293082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291757, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291757, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291759 q = 0) : d293084 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291759, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291759, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291760 q = 0) : d293085 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291760, d293085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291760, d293085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30810 (p : Pattern) (selected : d291764 p = 0) : d293089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291755 q = 0) : d293080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291756 q = 0) : d293081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291759 q = 0) : d293084 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291759, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291759, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291764 q = 0) : d293089 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291764, d293089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291764, d293089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30811 (p : Pattern) (selected : d291771 p = 0) : d293096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291761 q = 0) : d293086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291761, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30808 q selected
    | true =>
      simp only [d291761, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30809 q selected
  have h2 (q : Pattern) (selected : d291762 q = 0) : d293087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291762, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291762, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291763 q = 0) : d293088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291763, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291763, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291765 q = 0) : d293090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30809 q selected
    | true =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30810 q selected
  have h5 (q : Pattern) (selected : d291766 q = 0) : d293091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291767 q = 0) : d293092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291768 q = 0) : d293093 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291768, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291768, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291769 q = 0) : d293094 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291769, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291769, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291770 q = 0) : d293095 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291770, d293095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291770, d293095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291771 q = 0) : d293096 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291771, d293096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291771, d293096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30812 (p : Pattern) (selected : d291775 p = 0) : d293100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291765 q = 0) : d293090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30809 q selected
    | true =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30810 q selected
  have h2 (q : Pattern) (selected : d291766 q = 0) : d293091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291767 q = 0) : d293092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291769 q = 0) : d293094 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291769, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291769, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291774 q = 0) : d293099 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291774, d293099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291774, d293099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291775 q = 0) : d293100 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291775, d293100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291775, d293100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30813 (p : Pattern) (selected : d291781 p = 0) : d293106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291778 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291779 q = 0) : d293104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291780 q = 0) : d293105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291780, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291780, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291781 q = 0) : d293106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291781, d293106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291781, d293106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30814 (p : Pattern) (selected : d291785 p = 0) : d293110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291782 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291783 q = 0) : d293108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291784 q = 0) : d293109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291784, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291784, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291785 q = 0) : d293110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291785, d293110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291785, d293110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30815 (p : Pattern) (selected : d291791 p = 0) : d293116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291786 q = 0) : d293111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291786, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30813 q selected
    | true =>
      simp only [d291786, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30814 q selected
  have h2 (q : Pattern) (selected : d291787 q = 0) : d293112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291787, d293112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291787, d293112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291788 q = 0) : d293113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291788, d293113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291788, d293113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291789 q = 0) : d293114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291789, d293114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291789, d293114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291790 q = 0) : d293115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291790, d293115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291790, d293115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291791 q = 0) : d293116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291791, d293116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291791, d293116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30816 (p : Pattern) (selected : d291794 p = 0) : d293119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291778 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291779 q = 0) : d293104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291780 q = 0) : d293105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291780, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291780, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291794 q = 0) : d293119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291794, d293119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291794, d293119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30817 (p : Pattern) (selected : d291795 p = 0) : d293120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291782 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291783 q = 0) : d293108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291784 q = 0) : d293109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291784, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291784, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291795 q = 0) : d293120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291795, d293120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291795, d293120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30818 (p : Pattern) (selected : d291801 p = 0) : d293126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291786 q = 0) : d293111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291786, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30813 q selected
    | true =>
      simp only [d291786, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30814 q selected
  have h2 (q : Pattern) (selected : d291787 q = 0) : d293112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291787, d293112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291787, d293112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291788 q = 0) : d293113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291788, d293113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291788, d293113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291789 q = 0) : d293114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291789, d293114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291789, d293114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291790 q = 0) : d293115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291790, d293115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291790, d293115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291796 q = 0) : d293121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291796, d293121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30816 q selected
    | true =>
      simp only [d291796, d293121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30817 q selected
  have h7 (q : Pattern) (selected : d291797 q = 0) : d293122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291797, d293122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291797, d293122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291798 q = 0) : d293123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291798, d293123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291798, d293123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291799 q = 0) : d293124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291799, d293124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291799, d293124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291800 q = 0) : d293125 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291800, d293125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291800, d293125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291801 q = 0) : d293126 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291801, d293126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291801, d293126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30819 (p : Pattern) (selected : d291806 p = 0) : d293131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291778 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291779 q = 0) : d293104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291805 q = 0) : d293130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291805, d293130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291805, d293130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291806 q = 0) : d293131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291806, d293131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291806, d293131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30820 (p : Pattern) (selected : d291808 p = 0) : d293133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291782 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291783 q = 0) : d293108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291807 q = 0) : d293132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291807, d293132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291807, d293132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291808 q = 0) : d293133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291808, d293133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291808, d293133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30821 (p : Pattern) (selected : d291815 p = 0) : d293140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291778 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291813 q = 0) : d293138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291813, d293138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291813, d293138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291814 q = 0) : d293139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291814, d293139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291814, d293139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291815 q = 0) : d293140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291815, d293140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291815, d293140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30822 (p : Pattern) (selected : d291818 p = 0) : d293143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291782 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291816 q = 0) : d293141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291816, d293141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291816, d293141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291817 q = 0) : d293142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291817, d293142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291817, d293142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291818 q = 0) : d293143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291818, d293143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291818, d293143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30823 (p : Pattern) (selected : d291822 p = 0) : d293147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154503 q = 0) : d156196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154503, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154504 q = 0) : d156197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154504, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154594 q = 0) : d156287 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154594, d156287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154594, d156287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291748 q = 0) : d293073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291749 q = 0) : d293074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d291750 q = 0) : d293075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291750, d293075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291750, d293075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291822 q = 0) : d293147 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291822, d293147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291822, d293147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30824 (p : Pattern) (selected : d291828 p = 0) : d293153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291823 q = 0) : d293148 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291823, d293148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30823 q selected
    | true =>
      simp only [d291823, d293148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30808 q selected
  have h2 (q : Pattern) (selected : d291824 q = 0) : d293149 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291824, d293149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291824, d293149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291825 q = 0) : d293150 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291825, d293150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291825, d293150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291761 q = 0) : d293086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291761, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30808 q selected
    | true =>
      simp only [d291761, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30809 q selected
  have h5 (q : Pattern) (selected : d291762 q = 0) : d293087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291762, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291762, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291763 q = 0) : d293088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291763, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291763, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291826 q = 0) : d293151 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291826, d293151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291826, d293151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291765 q = 0) : d293090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30809 q selected
    | true =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30810 q selected
  have h9 (q : Pattern) (selected : d291766 q = 0) : d293091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291767 q = 0) : d293092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291768 q = 0) : d293093 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291768, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291768, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291827 q = 0) : d293152 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291827, d293152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291827, d293152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291828 q = 0) : d293153 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291828, d293153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291828, d293153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30825 (p : Pattern) (selected : d291834 p = 0) : d293159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291829 q = 0) : d293154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291829, d293154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30824 q selected
    | true =>
      simp only [d291829, d293154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291830 q = 0) : d293155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291830, d293155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291830, d293155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291831 q = 0) : d293156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291831, d293156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291831, d293156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291832 q = 0) : d293157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291832, d293157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291832, d293157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291833 q = 0) : d293158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291833, d293158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291833, d293158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291834 q = 0) : d293159 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291834, d293159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291834, d293159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30826 (p : Pattern) (selected : d291837 p = 0) : d293070 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro583 q selected
    | true =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro584 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2190 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro585 q selected
  have h3 (q : Pattern) (selected : d2191 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291836 q = 0) : d293069 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291836, d293069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291836, d293069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291837 q = 0) : d293070 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291837, d293070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291837, d293070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30827 (p : Pattern) (selected : d291844 p = 0) : d293077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2224 q = 0) : d53337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2224, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2224, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
  have h2 (q : Pattern) (selected : d2209 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h3 (q : Pattern) (selected : d2225 q = 0) : d53338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2225, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2225, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10514 q = 0) : d101726 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10514, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
    | true =>
      simp only [d10514, d101726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10515 q = 0) : d101727 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10515, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
    | true =>
      simp only [d10515, d101727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10516 q = 0) : d101728 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10516, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10516, d101728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291843 q = 0) : d293076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291843, d293076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291843, d293076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291844 q = 0) : d293077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291844, d293077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291844, d293077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30828 (p : Pattern) (selected : d291850 p = 0) : d293083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154623 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14051 q selected
    | true =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154624 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154625 q = 0) : d156196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154625, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154625, d156196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154626 q = 0) : d156197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154626, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154626, d156197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291838 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30826 q selected
    | true =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291839 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291840 q = 0) : d293073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291840, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291840, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291841 q = 0) : d293074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291841, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291841, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291842 q = 0) : d293075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291842, d293075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291842, d293075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291845 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
    | true =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291846 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291847 q = 0) : d293080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291847, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291847, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291848 q = 0) : d293081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291848, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291848, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291849 q = 0) : d293082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291849, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291849, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291850 q = 0) : d293083 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291850, d293083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291850, d293083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30829 (p : Pattern) (selected : d291852 p = 0) : d293085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291838 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30826 q selected
    | true =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291839 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291840 q = 0) : d293073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291840, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291840, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291841 q = 0) : d293074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291841, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291841, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291845 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
    | true =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291846 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291847 q = 0) : d293080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291847, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291847, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291848 q = 0) : d293081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291848, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291848, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291849 q = 0) : d293082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291849, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291849, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291851 q = 0) : d293084 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291851, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291851, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291852 q = 0) : d293085 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291852, d293085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291852, d293085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30830 (p : Pattern) (selected : d291856 p = 0) : d293089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291845 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
    | true =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291846 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291847 q = 0) : d293080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291847, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291847, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291848 q = 0) : d293081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291848, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291848, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291851 q = 0) : d293084 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291851, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291851, d293084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291856 q = 0) : d293089 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291856, d293089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291856, d293089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30831 (p : Pattern) (selected : d291863 p = 0) : d293096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291853 q = 0) : d293086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291853, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30828 q selected
    | true =>
      simp only [d291853, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30829 q selected
  have h2 (q : Pattern) (selected : d291854 q = 0) : d293087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291854, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291854, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291855 q = 0) : d293088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291855, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291855, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291857 q = 0) : d293090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291857, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30829 q selected
    | true =>
      simp only [d291857, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30830 q selected
  have h5 (q : Pattern) (selected : d291858 q = 0) : d293091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291858, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291858, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291859 q = 0) : d293092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291859, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291859, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291860 q = 0) : d293093 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291860, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291860, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291861 q = 0) : d293094 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291861, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291861, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291862 q = 0) : d293095 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291862, d293095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291862, d293095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291863 q = 0) : d293096 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291863, d293096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291863, d293096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30832 (p : Pattern) (selected : d291867 p = 0) : d293100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291857 q = 0) : d293090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291857, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30829 q selected
    | true =>
      simp only [d291857, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30830 q selected
  have h2 (q : Pattern) (selected : d291858 q = 0) : d293091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291858, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291858, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291859 q = 0) : d293092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291859, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291859, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291861 q = 0) : d293094 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291861, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291861, d293094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291866 q = 0) : d293099 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291866, d293099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291866, d293099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291867 q = 0) : d293100 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291867, d293100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291867, d293100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30833 (p : Pattern) (selected : d291873 p = 0) : d293106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291864 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291864, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30831 q selected
    | true =>
      simp only [d291864, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291865 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291865, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291865, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291868 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30832 q selected
    | true =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291869 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291870 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291870, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291870, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291871 q = 0) : d293104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291871, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291871, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291872 q = 0) : d293105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291872, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291872, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291873 q = 0) : d293106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291873, d293106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291873, d293106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30834 (p : Pattern) (selected : d291877 p = 0) : d293110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291868 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30832 q selected
    | true =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291869 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291874 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291874, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291874, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291875 q = 0) : d293108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291875, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291875, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291876 q = 0) : d293109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291876, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291876, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291877 q = 0) : d293110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291877, d293110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291877, d293110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30835 (p : Pattern) (selected : d291880 p = 0) : d293162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291748 q = 0) : d293073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291748, d293073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291749 q = 0) : d293074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291749, d293074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291755 q = 0) : d293080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291755, d293080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291756 q = 0) : d293081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291756, d293081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291757 q = 0) : d293082 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291757, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291757, d293082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d154526 q = 0) : d156219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14031 q selected
    | true =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d154527 q = 0) : d156220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d154528 q = 0) : d156221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154528, d156221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154528, d156221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d154529 q = 0) : d156222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154529, d156222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d154529, d156222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d154530 q = 0) : d156223 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154530, d156223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d154530, d156223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291880 q = 0) : d293162 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291880, d293162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291880, d293162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30836 (p : Pattern) (selected : d291886 p = 0) : d293168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291761 q = 0) : d293086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291761, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30808 q selected
    | true =>
      simp only [d291761, d293086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30809 q selected
  have h2 (q : Pattern) (selected : d291762 q = 0) : d293087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291762, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291762, d293087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291763 q = 0) : d293088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291763, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291763, d293088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291765 q = 0) : d293090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30809 q selected
    | true =>
      simp only [d291765, d293090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30810 q selected
  have h5 (q : Pattern) (selected : d291766 q = 0) : d293091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291766, d293091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291767 q = 0) : d293092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291767, d293092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291768 q = 0) : d293093 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291768, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291768, d293093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291881 q = 0) : d293163 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291881, d293163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30835 q selected
    | true =>
      simp only [d291881, d293163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14032 q selected
  have h9 (q : Pattern) (selected : d291882 q = 0) : d293164 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291882, d293164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291882, d293164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291883 q = 0) : d293165 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291883, d293165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291883, d293165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291884 q = 0) : d293166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291884, d293166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291884, d293166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291885 q = 0) : d293167 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291885, d293167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291885, d293167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291886 q = 0) : d293168 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291886, d293168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291886, d293168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30837 (p : Pattern) (selected : d291892 p = 0) : d293174 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291887 q = 0) : d293169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291887, d293169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30836 q selected
    | true =>
      simp only [d291887, d293169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291888 q = 0) : d293170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291888, d293170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291888, d293170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291889 q = 0) : d293171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291889, d293171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291889, d293171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291890 q = 0) : d293172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291890, d293172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291890, d293172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291891 q = 0) : d293173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291891, d293173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291891, d293173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291892 q = 0) : d293174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291892, d293174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291892, d293174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30838 (p : Pattern) (selected : d291898 p = 0) : d293180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291809 q = 0) : d293134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291809, d293134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30819 q selected
    | true =>
      simp only [d291809, d293134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30820 q selected
  have h2 (q : Pattern) (selected : d291810 q = 0) : d293135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291810, d293135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291810, d293135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291811 q = 0) : d293136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291811, d293136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291811, d293136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291812 q = 0) : d293137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291812, d293137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291812, d293137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291819 q = 0) : d293144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291819, d293144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30821 q selected
    | true =>
      simp only [d291819, d293144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30822 q selected
  have h6 (q : Pattern) (selected : d291820 q = 0) : d293145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291820, d293145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291820, d293145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291821 q = 0) : d293146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291821, d293146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291821, d293146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291835 q = 0) : d293160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291835, d293160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30825 q selected
    | true =>
      simp only [d291835, d293160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30813 q selected
  have h9 (q : Pattern) (selected : d291878 q = 0) : d293111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291878, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30833 q selected
    | true =>
      simp only [d291878, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30834 q selected
  have h10 (q : Pattern) (selected : d291879 q = 0) : d293161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291879, d293161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291879, d293161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291893 q = 0) : d293175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291893, d293175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30837 q selected
    | true =>
      simp only [d291893, d293175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291894 q = 0) : d293176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291894, d293176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291894, d293176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291895 q = 0) : d293177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291895, d293177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291895, d293177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291896 q = 0) : d293178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291896, d293178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291896, d293178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291897 q = 0) : d293179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291897, d293179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291897, d293179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291898 q = 0) : d293180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291898, d293180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291898, d293180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro30839 (p : Pattern) (selected : d291899 p = 0) : d293181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291778 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291779 q = 0) : d293104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291779, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291805 q = 0) : d293130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291805, d293130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291805, d293130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291899 q = 0) : d293181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291899, d293181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291899, d293181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30840 (p : Pattern) (selected : d291900 p = 0) : d293182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291782 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291783 q = 0) : d293108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291783, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291807 q = 0) : d293132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291807, d293132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291807, d293132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291900 q = 0) : d293182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291900, d293182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291900, d293182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30841 (p : Pattern) (selected : d291905 p = 0) : d293187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291778 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291778, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291813 q = 0) : d293138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291813, d293138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291813, d293138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291814 q = 0) : d293139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291814, d293139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291814, d293139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291905 q = 0) : d293187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291905, d293187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291905, d293187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30842 (p : Pattern) (selected : d291906 p = 0) : d293188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291776 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30812 q selected
    | true =>
      simp only [d291776, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291777 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291777, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291782 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291782, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291816 q = 0) : d293141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291816, d293141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291816, d293141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291817 q = 0) : d293142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291817, d293142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291817, d293142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291906 q = 0) : d293188 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291906, d293188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291906, d293188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30843 (p : Pattern) (selected : d291910 p = 0) : d293192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291829 q = 0) : d293154 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291829, d293154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30824 q selected
    | true =>
      simp only [d291829, d293154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291830 q = 0) : d293155 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291830, d293155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291830, d293155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291772 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30811 q selected
    | true =>
      simp only [d291772, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291773 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291773, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291831 q = 0) : d293156 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291831, d293156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291831, d293156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291832 q = 0) : d293157 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291832, d293157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291832, d293157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291833 q = 0) : d293158 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291833, d293158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291833, d293158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291910 q = 0) : d293192 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291910, d293192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291910, d293192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30844 (p : Pattern) (selected : d291912 p = 0) : d293119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291864 q = 0) : d293097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291864, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30831 q selected
    | true =>
      simp only [d291864, d293097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291865 q = 0) : d293098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291865, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291865, d293098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291868 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30832 q selected
    | true =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291869 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291870 q = 0) : d293103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291870, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291870, d293103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291871 q = 0) : d293104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291871, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291871, d293104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291872 q = 0) : d293105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291872, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291872, d293105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291912 q = 0) : d293119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291912, d293119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291912, d293119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30845 (p : Pattern) (selected : d291913 p = 0) : d293120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291868 q = 0) : d293101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30832 q selected
    | true =>
      simp only [d291868, d293101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291869 q = 0) : d293102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, d293102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291874 q = 0) : d293107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291874, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291874, d293107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291875 q = 0) : d293108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291875, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291875, d293108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291876 q = 0) : d293109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291876, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291876, d293109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291913 q = 0) : d293120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291913, d293120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291913, d293120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30846 (p : Pattern) (selected : d291916 p = 0) : d293195 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291887 q = 0) : d293169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291887, d293169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30836 q selected
    | true =>
      simp only [d291887, d293169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291888 q = 0) : d293170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291888, d293170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291888, d293170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291889 q = 0) : d293171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291889, d293171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291889, d293171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291890 q = 0) : d293172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291890, d293172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291890, d293172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291891 q = 0) : d293173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291891, d293173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291891, d293173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291916 q = 0) : d293195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291916, d293195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291916, d293195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30847 (p : Pattern) (selected : d291922 p = 0) : d293201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291809 q = 0) : d293134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291809, d293134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30819 q selected
    | true =>
      simp only [d291809, d293134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30820 q selected
  have h2 (q : Pattern) (selected : d291810 q = 0) : d293135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291810, d293135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291810, d293135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291811 q = 0) : d293136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291811, d293136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291811, d293136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291812 q = 0) : d293137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291812, d293137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291812, d293137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291819 q = 0) : d293144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291819, d293144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30821 q selected
    | true =>
      simp only [d291819, d293144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30822 q selected
  have h6 (q : Pattern) (selected : d291820 q = 0) : d293145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291820, d293145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291820, d293145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291821 q = 0) : d293146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291821, d293146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291821, d293146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291835 q = 0) : d293160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291835, d293160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30825 q selected
    | true =>
      simp only [d291835, d293160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30813 q selected
  have h9 (q : Pattern) (selected : d291878 q = 0) : d293111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291878, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30833 q selected
    | true =>
      simp only [d291878, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30834 q selected
  have h10 (q : Pattern) (selected : d291879 q = 0) : d293161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291879, d293161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291879, d293161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291893 q = 0) : d293175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291893, d293175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30837 q selected
    | true =>
      simp only [d291893, d293175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291894 q = 0) : d293176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291894, d293176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291894, d293176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291895 q = 0) : d293177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291895, d293177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291895, d293177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291896 q = 0) : d293178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291896, d293178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291896, d293178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291897 q = 0) : d293179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291897, d293179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291897, d293179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291901 q = 0) : d293183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291901, d293183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30839 q selected
    | true =>
      simp only [d291901, d293183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30840 q selected
  have h17 (q : Pattern) (selected : d291902 q = 0) : d293184 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291902, d293184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291902, d293184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d291903 q = 0) : d293185 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291903, d293185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d291903, d293185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d291904 q = 0) : d293186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291904, d293186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291904, d293186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d291907 q = 0) : d293189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291907, d293189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30841 q selected
    | true =>
      simp only [d291907, d293189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30842 q selected
  have h21 (q : Pattern) (selected : d291908 q = 0) : d293190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291908, d293190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291908, d293190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d291909 q = 0) : d293191 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291909, d293191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d291909, d293191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d291911 q = 0) : d293193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291911, d293193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30843 q selected
    | true =>
      simp only [d291911, d293193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30816 q selected
  have h24 (q : Pattern) (selected : d291914 q = 0) : d293121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291914, d293121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30844 q selected
    | true =>
      simp only [d291914, d293121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30845 q selected
  have h25 (q : Pattern) (selected : d291915 q = 0) : d293194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291915, d293194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d291915, d293194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d291917 q = 0) : d293196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291917, d293196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30846 q selected
    | true =>
      simp only [d291917, d293196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d291918 q = 0) : d293197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291918, d293197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d291918, d293197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d291919 q = 0) : d293198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291919, d293198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d291919, d293198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d291920 q = 0) : d293199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291920, d293199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d291920, d293199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d291921 q = 0) : d293200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291921, d293200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d291921, d293200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d291922 q = 0) : d293201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291922, d293201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291922, d293201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro30848 (p : Pattern) (selected : d291929 p = 0) : d293208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291786 q = 0) : d293111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291786, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30813 q selected
    | true =>
      simp only [d291786, d293111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30814 q selected
  have h2 (q : Pattern) (selected : d291787 q = 0) : d293112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291787, d293112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291787, d293112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291788 q = 0) : d293113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291788, d293113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291788, d293113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291789 q = 0) : d293114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291789, d293114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291789, d293114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291790 q = 0) : d293115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291790, d293115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291790, d293115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291924 q = 0) : d293203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291924, d293203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30814 q selected
    | true =>
      simp only [d291924, d293203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291925 q = 0) : d293204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291925, d293204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291925, d293204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291926 q = 0) : d293205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291926, d293205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291926, d293205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291927 q = 0) : d293206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291927, d293206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291927, d293206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291928 q = 0) : d293207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291928, d293207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291928, d293207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291929 q = 0) : d293208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291929, d293208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291929, d293208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30849 (p : Pattern) (selected : d291935 p = 0) : d293214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291924 q = 0) : d293203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291924, d293203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30814 q selected
    | true =>
      simp only [d291924, d293203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291925 q = 0) : d293204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291925, d293204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291925, d293204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291926 q = 0) : d293205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291926, d293205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291926, d293205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291927 q = 0) : d293206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291927, d293206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291927, d293206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291928 q = 0) : d293207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291928, d293207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291928, d293207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291930 q = 0) : d293209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291930, d293209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30817 q selected
    | true =>
      simp only [d291930, d293209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291931 q = 0) : d293210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291931, d293210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291931, d293210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291932 q = 0) : d293211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291932, d293211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291932, d293211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291933 q = 0) : d293212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291933, d293212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291933, d293212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291934 q = 0) : d293213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291934, d293213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291934, d293213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291935 q = 0) : d293214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291935, d293214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291935, d293214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30850 (p : Pattern) (selected : d291942 p = 0) : d293221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291911 q = 0) : d293193 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291911, d293193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30843 q selected
    | true =>
      simp only [d291911, d293193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30816 q selected
  have h2 (q : Pattern) (selected : d291914 q = 0) : d293121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291914, d293121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30844 q selected
    | true =>
      simp only [d291914, d293121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30845 q selected
  have h3 (q : Pattern) (selected : d291915 q = 0) : d293194 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291915, d293194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291915, d293194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291917 q = 0) : d293196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291917, d293196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30846 q selected
    | true =>
      simp only [d291917, d293196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291918 q = 0) : d293197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291918, d293197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291918, d293197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291919 q = 0) : d293198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291919, d293198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291919, d293198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291940 q = 0) : d293219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291940, d293219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291940, d293219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291941 q = 0) : d293220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291941, d293220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291941, d293220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291942 q = 0) : d293221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291942, d293221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291942, d293221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30851 (p : Pattern) (selected : d291944 p = 0) : d293223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291930 q = 0) : d293209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291930, d293209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30817 q selected
    | true =>
      simp only [d291930, d293209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291931 q = 0) : d293210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291931, d293210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291931, d293210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291932 q = 0) : d293211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291932, d293211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291932, d293211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291933 q = 0) : d293212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291933, d293212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291933, d293212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291934 q = 0) : d293213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291934, d293213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291934, d293213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291944 q = 0) : d293223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291944, d293223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291944, d293223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30852 (p : Pattern) (selected : d291955 p = 0) : d293234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154749 q = 0) : d156379 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
  have h2 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154750 q = 0) : d156380 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154751 q = 0) : d156381 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154752 q = 0) : d156382 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d154753 q = 0) : d156383 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154753, d156383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154753, d156383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291950 q = 0) : d293229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
  have h9 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d291951 q = 0) : d293230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291952 q = 0) : d293231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291953 q = 0) : d293232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291954 q = 0) : d293233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291954, d293233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291954, d293233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291955 q = 0) : d293234 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291955, d293234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291955, d293234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30853 (p : Pattern) (selected : d291961 p = 0) : d293240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154749 q = 0) : d156379 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154749, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
  have h2 (q : Pattern) (selected : d154501 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14026 q selected
    | true =>
      simp only [d154501, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154750 q = 0) : d156380 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154750, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154502 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154502, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154751 q = 0) : d156381 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154751, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154752 q = 0) : d156382 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154752, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291950 q = 0) : d293229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
  have h8 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291951 q = 0) : d293230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291952 q = 0) : d293231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291953 q = 0) : d293232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291954 q = 0) : d293233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291954, d293233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291954, d293233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291956 q = 0) : d293235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
  have h15 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291957 q = 0) : d293236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291958 q = 0) : d293237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291959 q = 0) : d293238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291960 q = 0) : d293239 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291960, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291960, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291961 q = 0) : d293240 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291961, d293240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291961, d293240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30854 (p : Pattern) (selected : d291966 p = 0) : d293245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291950 q = 0) : d293229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
  have h2 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291951 q = 0) : d293230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291952 q = 0) : d293231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291953 q = 0) : d293232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291956 q = 0) : d293235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
  have h8 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291957 q = 0) : d293236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291958 q = 0) : d293237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291959 q = 0) : d293238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291960 q = 0) : d293239 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291960, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291960, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291965 q = 0) : d293244 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291965, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291965, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291966 q = 0) : d293245 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291966, d293245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291966, d293245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30855 (p : Pattern) (selected : d291971 p = 0) : d293250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291956 q = 0) : d293235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
  have h2 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291957 q = 0) : d293236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291958 q = 0) : d293237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291959 q = 0) : d293238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291965 q = 0) : d293244 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291965, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291965, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291971 q = 0) : d293250 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291971, d293250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291971, d293250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30856 (p : Pattern) (selected : d291977 p = 0) : d293256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291962 q = 0) : d293241 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291962, d293241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30852 q selected
    | true =>
      simp only [d291962, d293241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30853 q selected
  have h2 (q : Pattern) (selected : d291963 q = 0) : d293242 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291963, d293242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291963, d293242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291964 q = 0) : d293243 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291964, d293243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291964, d293243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291967 q = 0) : d293246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291967, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30853 q selected
    | true =>
      simp only [d291967, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30854 q selected
  have h5 (q : Pattern) (selected : d291968 q = 0) : d293247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291968, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291968, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291969 q = 0) : d293248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291969, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291969, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291970 q = 0) : d293249 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291970, d293249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291970, d293249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291972 q = 0) : d293251 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30854 q selected
    | true =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30855 q selected
  have h9 (q : Pattern) (selected : d291973 q = 0) : d293252 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291974 q = 0) : d293253 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291975 q = 0) : d293254 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291975, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291975, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291976 q = 0) : d293255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291976, d293255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291976, d293255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291977 q = 0) : d293256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291977, d293256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291977, d293256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30857 (p : Pattern) (selected : d291982 p = 0) : d293261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291967 q = 0) : d293246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291967, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30853 q selected
    | true =>
      simp only [d291967, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30854 q selected
  have h2 (q : Pattern) (selected : d291968 q = 0) : d293247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291968, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291968, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291969 q = 0) : d293248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291969, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291969, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291972 q = 0) : d293251 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30854 q selected
    | true =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30855 q selected
  have h5 (q : Pattern) (selected : d291973 q = 0) : d293252 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291974 q = 0) : d293253 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291975 q = 0) : d293254 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291975, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291975, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291980 q = 0) : d293259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291980, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291980, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291981 q = 0) : d293260 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291981, d293260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291981, d293260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291982 q = 0) : d293261 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291982, d293261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291982, d293261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30858 (p : Pattern) (selected : d291988 p = 0) : d293267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291978 q = 0) : d293257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291978, d293257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30856 q selected
    | true =>
      simp only [d291978, d293257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291979 q = 0) : d293258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291979, d293258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291979, d293258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291983 q = 0) : d293262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291983, d293262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30857 q selected
    | true =>
      simp only [d291983, d293262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291984 q = 0) : d293263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291984, d293263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291984, d293263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291985 q = 0) : d293264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291985, d293264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291985, d293264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291986 q = 0) : d293265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291986, d293265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291986, d293265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291987 q = 0) : d293266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291987, d293266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291987, d293266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291988 q = 0) : d293267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291988, d293267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291988, d293267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30859 (p : Pattern) (selected : d291990 p = 0) : d293269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291972 q = 0) : d293251 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30854 q selected
    | true =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30855 q selected
  have h2 (q : Pattern) (selected : d291973 q = 0) : d293252 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291974 q = 0) : d293253 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291980 q = 0) : d293259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291980, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291980, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291989 q = 0) : d293268 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291989, d293268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291989, d293268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291990 q = 0) : d293269 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291990, d293269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291990, d293269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30860 (p : Pattern) (selected : d291996 p = 0) : d293275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291983 q = 0) : d293262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291983, d293262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30857 q selected
    | true =>
      simp only [d291983, d293262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291984 q = 0) : d293263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291984, d293263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291984, d293263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291991 q = 0) : d293270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291991, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30859 q selected
    | true =>
      simp only [d291991, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291992 q = 0) : d293271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291992, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291992, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291993 q = 0) : d293272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291993, d293272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291993, d293272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291994 q = 0) : d293273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291994, d293273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291994, d293273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291995 q = 0) : d293274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291995, d293274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291995, d293274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291996 q = 0) : d293275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291996, d293275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291996, d293275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30861 (p : Pattern) (selected : d292008 p = 0) : d293240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d154815 q = 0) : d156379 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154815, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154815, d156379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14051 q selected
  have h2 (q : Pattern) (selected : d154623 q = 0) : d156194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14051 q selected
    | true =>
      simp only [d154623, d156194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154816 q = 0) : d156380 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154816, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154816, d156380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154624 q = 0) : d156195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154624, d156195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154817 q = 0) : d156381 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154817, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154817, d156381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154818 q = 0) : d156382 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154818, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154818, d156382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291998 q = 0) : d293229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291998, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291998, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30826 q selected
  have h8 (q : Pattern) (selected : d291838 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30826 q selected
    | true =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291999 q = 0) : d293230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291999, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291999, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291839 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d292000 q = 0) : d293231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292000, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d292000, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d292001 q = 0) : d293232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292001, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d292001, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d292002 q = 0) : d293233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292002, d293233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292002, d293233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d292003 q = 0) : d293235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292003, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292003, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
  have h15 (q : Pattern) (selected : d291845 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
    | true =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d292004 q = 0) : d293236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292004, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d292004, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291846 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d292005 q = 0) : d293237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292005, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d292005, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d292006 q = 0) : d293238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292006, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d292006, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d292007 q = 0) : d293239 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292007, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d292007, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d292008 q = 0) : d293240 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292008, d293240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d292008, d293240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30862 (p : Pattern) (selected : d292010 p = 0) : d293245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291998 q = 0) : d293229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291998, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291998, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30826 q selected
  have h2 (q : Pattern) (selected : d291838 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30826 q selected
    | true =>
      simp only [d291838, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291999 q = 0) : d293230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291999, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291999, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291839 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291839, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292000 q = 0) : d293231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292000, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292000, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292001 q = 0) : d293232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292001, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292001, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d292003 q = 0) : d293235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292003, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292003, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
  have h8 (q : Pattern) (selected : d291845 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
    | true =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d292004 q = 0) : d293236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292004, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292004, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291846 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d292005 q = 0) : d293237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292005, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d292005, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d292006 q = 0) : d293238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292006, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d292006, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d292007 q = 0) : d293239 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292007, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292007, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d292009 q = 0) : d293244 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292009, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d292009, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d292010 q = 0) : d293245 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292010, d293245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d292010, d293245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30863 (p : Pattern) (selected : d292014 p = 0) : d293250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292003 q = 0) : d293235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292003, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292003, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
  have h2 (q : Pattern) (selected : d291845 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30827 q selected
    | true =>
      simp only [d291845, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292004 q = 0) : d293236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292004, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292004, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291846 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291846, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292005 q = 0) : d293237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292005, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292005, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292006 q = 0) : d293238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292006, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292006, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d292009 q = 0) : d293244 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292009, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292009, d293244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d292014 q = 0) : d293250 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292014, d293250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292014, d293250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30864 (p : Pattern) (selected : d292021 p = 0) : d293261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292011 q = 0) : d293246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292011, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30861 q selected
    | true =>
      simp only [d292011, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30862 q selected
  have h2 (q : Pattern) (selected : d292012 q = 0) : d293247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292012, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292012, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292013 q = 0) : d293248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292013, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292013, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292015 q = 0) : d293251 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292015, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30862 q selected
    | true =>
      simp only [d292015, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30863 q selected
  have h5 (q : Pattern) (selected : d292016 q = 0) : d293252 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292016, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292016, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292017 q = 0) : d293253 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292017, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292017, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d292018 q = 0) : d293254 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292018, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292018, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d292019 q = 0) : d293259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292019, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292019, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d292020 q = 0) : d293260 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292020, d293260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292020, d293260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d292021 q = 0) : d293261 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292021, d293261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d292021, d293261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30865 (p : Pattern) (selected : d292025 p = 0) : d293269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292015 q = 0) : d293251 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292015, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30862 q selected
    | true =>
      simp only [d292015, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30863 q selected
  have h2 (q : Pattern) (selected : d292016 q = 0) : d293252 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292016, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292016, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292017 q = 0) : d293253 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292017, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292017, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292019 q = 0) : d293259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292019, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292019, d293259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292024 q = 0) : d293268 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292024, d293268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292024, d293268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292025 q = 0) : d293269 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292025, d293269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292025, d293269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30866 (p : Pattern) (selected : d292031 p = 0) : d293275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292022 q = 0) : d293262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292022, d293262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30864 q selected
    | true =>
      simp only [d292022, d293262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292023 q = 0) : d293263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292023, d293263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292023, d293263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292026 q = 0) : d293270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292026, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30865 q selected
    | true =>
      simp only [d292026, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292027 q = 0) : d293271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292027, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292027, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d292028 q = 0) : d293272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292028, d293272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292028, d293272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292029 q = 0) : d293273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292029, d293273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292029, d293273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d292030 q = 0) : d293274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292030, d293274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292030, d293274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d292031 q = 0) : d293275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292031, d293275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292031, d293275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30867 (p : Pattern) (selected : d292035 p = 0) : d293280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292026 q = 0) : d293270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292026, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30865 q selected
    | true =>
      simp only [d292026, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292027 q = 0) : d293271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292027, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292027, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292032 q = 0) : d293277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292032, d293277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292032, d293277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292033 q = 0) : d293278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292033, d293278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292033, d293278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292034 q = 0) : d293279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292034, d293279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292034, d293279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292035 q = 0) : d293280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292035, d293280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292035, d293280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30868 (p : Pattern) (selected : d292038 p = 0) : d293283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291950 q = 0) : d293229 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291950, d293229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
  have h2 (q : Pattern) (selected : d291746 q = 0) : d293071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30806 q selected
    | true =>
      simp only [d291746, d293071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291951 q = 0) : d293230 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291951, d293230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291747 q = 0) : d293072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291747, d293072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291952 q = 0) : d293231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291952, d293231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291953 q = 0) : d293232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291953, d293232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291956 q = 0) : d293235 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291956, d293235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
  have h8 (q : Pattern) (selected : d291753 q = 0) : d293078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30807 q selected
    | true =>
      simp only [d291753, d293078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291957 q = 0) : d293236 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291957, d293236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291754 q = 0) : d293079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291754, d293079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291958 q = 0) : d293237 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291958, d293237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291959 q = 0) : d293238 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291959, d293238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291960 q = 0) : d293239 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291960, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291960, d293239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d154777 q = 0) : d156407 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154777, d156407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154777, d156407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14031 q selected
  have h15 (q : Pattern) (selected : d154526 q = 0) : d156219 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14031 q selected
    | true =>
      simp only [d154526, d156219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d154778 q = 0) : d156408 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154778, d156408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d154778, d156408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d154527 q = 0) : d156220 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d154527, d156220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d154779 q = 0) : d156409 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154779, d156409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d154779, d156409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d154780 q = 0) : d156410 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154780, d156410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d154780, d156410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d154781 q = 0) : d156411 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d154781, d156411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d154781, d156411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d292038 q = 0) : d293283 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292038, d293283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d292038, d293283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30869 (p : Pattern) (selected : d292044 p = 0) : d293289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291967 q = 0) : d293246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291967, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30853 q selected
    | true =>
      simp only [d291967, d293246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30854 q selected
  have h2 (q : Pattern) (selected : d291968 q = 0) : d293247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291968, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291968, d293247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291969 q = 0) : d293248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291969, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291969, d293248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291972 q = 0) : d293251 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30854 q selected
    | true =>
      simp only [d291972, d293251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30855 q selected
  have h5 (q : Pattern) (selected : d291973 q = 0) : d293252 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291973, d293252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291974 q = 0) : d293253 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291974, d293253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291975 q = 0) : d293254 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291975, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291975, d293254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d292039 q = 0) : d293284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292039, d293284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30868 q selected
    | true =>
      simp only [d292039, d293284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14082 q selected
  have h9 (q : Pattern) (selected : d292040 q = 0) : d293285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292040, d293285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292040, d293285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d292041 q = 0) : d293286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292041, d293286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292041, d293286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d292042 q = 0) : d293287 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292042, d293287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d292042, d293287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d292043 q = 0) : d293288 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292043, d293288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292043, d293288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d292044 q = 0) : d293289 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292044, d293289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d292044, d293289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro30870 (p : Pattern) (selected : d292050 p = 0) : d293295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292045 q = 0) : d293290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292045, d293290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30869 q selected
    | true =>
      simp only [d292045, d293290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292046 q = 0) : d293291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292046, d293291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292046, d293291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292047 q = 0) : d293292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292047, d293292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292047, d293292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292048 q = 0) : d293293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292048, d293293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292048, d293293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292049 q = 0) : d293294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292049, d293294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292049, d293294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292050 q = 0) : d293295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292050, d293295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292050, d293295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30871 (p : Pattern) (selected : d292056 p = 0) : d293301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291997 q = 0) : d293276 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291997, d293276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30858 q selected
    | true =>
      simp only [d291997, d293276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30860 q selected
  have h2 (q : Pattern) (selected : d292036 q = 0) : d293281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292036, d293281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30866 q selected
    | true =>
      simp only [d292036, d293281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30867 q selected
  have h3 (q : Pattern) (selected : d292037 q = 0) : d293282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292037, d293282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292037, d293282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292051 q = 0) : d293296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292051, d293296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30870 q selected
    | true =>
      simp only [d292051, d293296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292052 q = 0) : d293297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292052, d293297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292052, d293297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292053 q = 0) : d293298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292053, d293298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292053, d293298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d292054 q = 0) : d293299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292054, d293299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292054, d293299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d292055 q = 0) : d293300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292055, d293300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292055, d293300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d292056 q = 0) : d293301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292056, d293301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292056, d293301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro30872 (p : Pattern) (selected : d292061 p = 0) : d293280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291991 q = 0) : d293270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291991, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30859 q selected
    | true =>
      simp only [d291991, d293270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291992 q = 0) : d293271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291992, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291992, d293271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292058 q = 0) : d293277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292058, d293277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292058, d293277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292059 q = 0) : d293278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292059, d293278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292059, d293278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292060 q = 0) : d293279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292060, d293279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292060, d293279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292061 q = 0) : d293280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292061, d293280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292061, d293280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30873 (p : Pattern) (selected : d292067 p = 0) : d293308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292062 q = 0) : d293303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292062, d293303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30872 q selected
    | true =>
      simp only [d292062, d293303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292063 q = 0) : d293304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292063, d293304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292063, d293304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292064 q = 0) : d293305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292064, d293305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292064, d293305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292065 q = 0) : d293306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292065, d293306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292065, d293306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d292066 q = 0) : d293307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292066, d293307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292066, d293307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292067 q = 0) : d293308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292067, d293308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292067, d293308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30874 (p : Pattern) (selected : d292073 p = 0) : d293314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d291792 q = 0) : d293117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291792, d293117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291792, d293117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30815 q selected
  have h2 (q : Pattern) (selected : d291793 q = 0) : d293118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291793, d293118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291793, d293118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291802 q = 0) : d293127 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291802, d293127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30815 q selected
    | true =>
      simp only [d291802, d293127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30818 q selected
  have h4 (q : Pattern) (selected : d291803 q = 0) : d293128 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291803, d293128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291803, d293128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291804 q = 0) : d293129 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291804, d293129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291804, d293129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291923 q = 0) : d293202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291923, d293202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30838 q selected
    | true =>
      simp only [d291923, d293202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30847 q selected
  have h7 (q : Pattern) (selected : d291936 q = 0) : d293215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291936, d293215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30848 q selected
    | true =>
      simp only [d291936, d293215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30849 q selected
  have h8 (q : Pattern) (selected : d291937 q = 0) : d293216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291937, d293216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291937, d293216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291938 q = 0) : d293217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291938, d293217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291938, d293217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d291939 q = 0) : d293218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291939, d293218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291939, d293218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d291943 q = 0) : d293222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291943, d293222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291943, d293222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30850 q selected
  have h12 (q : Pattern) (selected : d291945 q = 0) : d293224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291945, d293224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291945, d293224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30851 q selected
  have h13 (q : Pattern) (selected : d291946 q = 0) : d293225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291946, d293225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291946, d293225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291947 q = 0) : d293226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291947, d293226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291947, d293226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291948 q = 0) : d293227 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291948, d293227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291948, d293227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291949 q = 0) : d293228 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291949, d293228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291949, d293228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d292057 q = 0) : d293302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292057, d293302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292057, d293302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30871 q selected
  have h18 (q : Pattern) (selected : d292068 q = 0) : d293309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292068, d293309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292068, d293309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30873 q selected
  have h19 (q : Pattern) (selected : d292069 q = 0) : d293310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292069, d293310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d292069, d293310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d292070 q = 0) : d293311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292070, d293311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d292070, d293311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d292071 q = 0) : d293312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292071, d293312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d292071, d293312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d292072 q = 0) : d293313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292072, d293313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d292072, d293313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d292073 q = 0) : d293314 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d292073, d293314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d292073, d293314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro30875 (p : Pattern) (selected : d292079 p = 0) : d293320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292074 q = 0) : d293315 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d292074, d293315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292074, d293315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30874 q selected
  have h2 (q : Pattern) (selected : d292075 q = 0) : d293316 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d292075, d293316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292075, d293316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292076 q = 0) : d293317 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d292076, d293317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292076, d293317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292077 q = 0) : d293318 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d292077, d293318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292077, d293318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d292078 q = 0) : d293319 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d292078, d293319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292078, d293319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292079 q = 0) : d293320 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d292079, d293320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292079, d293320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30876 (p : Pattern) (selected : d292085 p = 0) : d293326 p = 1 := by
  have h0 (q : Pattern) (selected : d290602 q = 0) : d292221 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290602, d292221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13765 q selected
    | true =>
      simp only [d290602, d292221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30587 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d290927 q = 0) : d292464 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290927, d292464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290927, d292464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30651 q selected
  have h3 (q : Pattern) (selected : d290928 q = 0) : d292465 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290928, d292465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290928, d292465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291323 q = 0) : d292754 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d291323, d292754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291323, d292754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30725 q selected
  have h5 (q : Pattern) (selected : d291324 q = 0) : d292755 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d291324, d292755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291324, d292755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291325 q = 0) : d292756 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d291325, d292756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291325, d292756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291740 q = 0) : d293065 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d291740, d293065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291740, d293065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30805 q selected
  have h8 (q : Pattern) (selected : d291741 q = 0) : d293066 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d291741, d293066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291741, d293066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291742 q = 0) : d293067 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d291742, d293067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291742, d293067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291743 q = 0) : d293068 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d291743, d293068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291743, d293068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d292080 q = 0) : d293321 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d292080, d293321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292080, d293321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30875 q selected
  have h12 (q : Pattern) (selected : d292081 q = 0) : d293322 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d292081, d293322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292081, d293322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d292082 q = 0) : d293323 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d292082, d293323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292082, d293323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d292083 q = 0) : d293324 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d292083, d293324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292083, d293324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d292084 q = 0) : d293325 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d292084, d293325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d292084, d293325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d292085 q = 0) : d293326 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d292085, d293326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d292085, d293326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro30877 (p : Pattern) (selected : d292091 p = 0) : d293332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292086 q = 0) : d293327 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d292086, d293327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30876 q selected
    | true =>
      simp only [d292086, d293327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292087 q = 0) : d293328 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d292087, d293328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292087, d293328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292088 q = 0) : d293329 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d292088, d293329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292088, d293329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292089 q = 0) : d293330 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d292089, d293330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292089, d293330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292090 q = 0) : d293331 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d292090, d293331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292090, d293331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292091 q = 0) : d293332 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d292091, d293332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292091, d293332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30878 (p : Pattern) (selected : d292097 p = 0) : d293338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292092 q = 0) : d293333 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d292092, d293333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30877 q selected
    | true =>
      simp only [d292092, d293333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292093 q = 0) : d293334 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d292093, d293334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292093, d293334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292094 q = 0) : d293335 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d292094, d293335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292094, d293335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292095 q = 0) : d293336 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d292095, d293336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292095, d293336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292096 q = 0) : d293337 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d292096, d293337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292096, d293337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292097 q = 0) : d293338 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d292097, d293338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292097, d293338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30879 (p : Pattern) (selected : d292103 p = 0) : d293344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292098 q = 0) : d293339 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d292098, d293339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30878 q selected
    | true =>
      simp only [d292098, d293339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292099 q = 0) : d293340 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d292099, d293340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292099, d293340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292100 q = 0) : d293341 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d292100, d293341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292100, d293341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292101 q = 0) : d293342 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d292101, d293342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292101, d293342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292102 q = 0) : d293343 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d292102, d293343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292102, d293343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292103 q = 0) : d293344 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d292103, d293344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292103, d293344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30880 (p : Pattern) (selected : d292109 p = 0) : d293350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292104 q = 0) : d293345 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d292104, d293345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30879 q selected
    | true =>
      simp only [d292104, d293345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292105 q = 0) : d293346 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d292105, d293346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292105, d293346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292106 q = 0) : d293347 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d292106, d293347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292106, d293347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292107 q = 0) : d293348 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d292107, d293348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292107, d293348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292108 q = 0) : d293349 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d292108, d293349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292108, d293349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292109 q = 0) : d293350 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d292109, d293350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292109, d293350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30881 (p : Pattern) (selected : d292115 p = 0) : d293356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292110 q = 0) : d293351 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d292110, d293351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30880 q selected
    | true =>
      simp only [d292110, d293351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292111 q = 0) : d293352 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d292111, d293352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292111, d293352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292112 q = 0) : d293353 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d292112, d293353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292112, d293353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292113 q = 0) : d293354 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d292113, d293354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292113, d293354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292114 q = 0) : d293355 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d292114, d293355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292114, d293355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292115 q = 0) : d293356 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d292115, d293356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292115, d293356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30882 (p : Pattern) (selected : d292121 p = 0) : d293362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292116 q = 0) : d293357 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d292116, d293357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30881 q selected
    | true =>
      simp only [d292116, d293357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292117 q = 0) : d293358 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d292117, d293358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292117, d293358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292118 q = 0) : d293359 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d292118, d293359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292118, d293359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292119 q = 0) : d293360 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d292119, d293360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292119, d293360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292120 q = 0) : d293361 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d292120, d293361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292120, d293361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292121 q = 0) : d293362 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d292121, d293362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292121, d293362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30883 (p : Pattern) (selected : d292127 p = 0) : d293368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d292122 q = 0) : d293363 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d292122, d293363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30882 q selected
    | true =>
      simp only [d292122, d293363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292123 q = 0) : d293364 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d292123, d293364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292123, d293364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292124 q = 0) : d293365 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d292124, d293365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292124, d293365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292125 q = 0) : d293366 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d292125, d293366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292125, d293366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292126 q = 0) : d293367 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d292126, d293367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292126, d293367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292127 q = 0) : d293368 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d292127, d293368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292127, d293368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30884 (p : Pattern) (selected : d290541 p = 1) : d295841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153115 q = 1) : d153115 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153121 q = 1) : d153121 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d290536 q = 1) : d290536 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d153170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14129 q selected
    | true =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14115 q selected
  have h5 (q : Pattern) (selected : d290537 q = 1) : d295837 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290537, d295837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290537, d295837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153177 q = 1) : d153177 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d290538 q = 1) : d295838 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290538, d295838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290538, d295838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290539 q = 1) : d295839 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290539, d295839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290539, d295839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290540 q = 1) : d295840 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290540, d295840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290540, d295840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290541 q = 1) : d295841 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290541, d295841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290541, d295841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro30885 (p : Pattern) (selected : d290548 p = 1) : d295846 p = 1 := by
  have h0 (q : Pattern) (selected : d153115 q = 1) : d153115 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153121 q = 1) : d153121 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d290536 q = 1) : d290536 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d153170 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14129 q selected
    | true =>
      simp only [d153170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14115 q selected
  have h4 (q : Pattern) (selected : d290537 q = 1) : d295837 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290537, d295837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290537, d295837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d153177 q = 1) : d153177 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d290538 q = 1) : d295838 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290538, d295838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290538, d295838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290539 q = 1) : d295839 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290539, d295839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290539, d295839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290540 q = 1) : d295840 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290540, d295840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290540, d295840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d153186 q = 1) : d153186 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d153190 q = 1) : d153190 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d290543 q = 1) : d290543 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d153194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14131 q selected
    | true =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14117 q selected
  have h13 (q : Pattern) (selected : d290544 q = 1) : d295842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290544, d295842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290544, d295842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153198 q = 1) : d153198 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d290545 q = 1) : d295843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290545, d295843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290545, d295843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290546 q = 1) : d295844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290546, d295844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290546, d295844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d290547 q = 1) : d295845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290547, d295845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290547, d295845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d290548 q = 1) : d295846 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290548, d295846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290548, d295846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro30886 (p : Pattern) (selected : d290555 p = 1) : d295853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290543 q = 1) : d290543 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14131 q selected
    | true =>
      simp only [d153194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14117 q selected
  have h3 (q : Pattern) (selected : d290544 q = 1) : d295842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290544, d295842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290544, d295842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153198 q = 1) : d153198 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d290545 q = 1) : d295843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290545, d295843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290545, d295843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290553 q = 1) : d295851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290553, d295851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290553, d295851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290554 q = 1) : d295852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290554, d295852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290554, d295852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290555 q = 1) : d295853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290555, d295853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290555, d295853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30887 (p : Pattern) (selected : d290589 p = 1) : d295863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290584 q = 1) : d290584 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d153261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14136 q selected
    | true =>
      simp only [d153261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14122 q selected
  have h3 (q : Pattern) (selected : d290585 q = 1) : d295859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290585, d295859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290585, d295859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153268 q = 1) : d153268 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d290586 q = 1) : d295860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290586, d295860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290586, d295860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290587 q = 1) : d295861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290587, d295861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290587, d295861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290588 q = 1) : d295862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290588, d295862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290588, d295862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290589 q = 1) : d295863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290589, d295863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290589, d295863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30888 (p : Pattern) (selected : d290595 p = 1) : d295869 p = 1 := by
  have h0 (q : Pattern) (selected : d153109 q = 1) : d153109 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290549 q = 1) : d295847 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290549, d295847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30884 q selected
    | true =>
      simp only [d290549, d295847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30885 q selected
  have h2 (q : Pattern) (selected : d153205 q = 1) : d153205 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d290550 q = 1) : d295848 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290550, d295848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290550, d295848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d290551 q = 1) : d295849 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290551, d295849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290551, d295849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290552 q = 1) : d295850 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290552, d295850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290552, d295850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290556 q = 1) : d295854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290556, d295854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290556, d295854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30886 q selected
  have h8 (q : Pattern) (selected : d153214 q = 1) : d153214 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d290557 q = 1) : d295855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290557, d295855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290557, d295855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290558 q = 1) : d295856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290558, d295856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290558, d295856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d290559 q = 1) : d295857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290559, d295857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290559, d295857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d290560 q = 1) : d295858 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290560, d295858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290560, d295858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290590 q = 1) : d295864 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290590, d295864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290590, d295864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30887 q selected
  have h14 (q : Pattern) (selected : d153279 q = 1) : d153279 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d290591 q = 1) : d295865 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290591, d295865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290591, d295865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290592 q = 1) : d295866 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290592, d295866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290592, d295866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d290593 q = 1) : d295867 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290593, d295867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d290593, d295867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d290594 q = 1) : d295868 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290594, d295868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d290594, d295868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d290595 q = 1) : d295869 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290595, d295869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290595, d295869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro30889 (p : Pattern) (selected : d290601 p = 1) : d295875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290596 q = 1) : d295870 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290596, d295870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290596, d295870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30888 q selected
  have h2 (q : Pattern) (selected : d290597 q = 1) : d295871 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290597, d295871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290597, d295871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290598 q = 1) : d295872 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290598, d295872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290598, d295872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290599 q = 1) : d295873 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290599, d295873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290599, d295873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290600 q = 1) : d295874 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290600, d295874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290600, d295874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290601 q = 1) : d295875 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290601, d295875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290601, d295875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30890 (p : Pattern) (selected : d290700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d568 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25812 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19156 q selected
    | true =>
      simp only [d25812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25813 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290699 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290700 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30891 (p : Pattern) (selected : d290706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290705 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d290705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290706 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d290706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro30892 (p : Pattern) (selected : d290713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30890 q selected
    | true =>
      simp only [d290701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290703 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290704 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290707 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30891 q selected
    | true =>
      simp only [d290707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290708 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290709 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290710 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290711 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290712 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290713 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30893 (p : Pattern) (selected : d290715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153152 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
    | true =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d153153 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153154 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153155 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290714 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290715 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30894 (p : Pattern) (selected : d290725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30892 q selected
    | true =>
      simp only [d290716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30893 q selected
  have h2 (q : Pattern) (selected : d290717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30893 q selected
    | true =>
      simp only [d290719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290724 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290725 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30895 (p : Pattern) (selected : d290729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30893 q selected
    | true =>
      simp only [d290719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290723 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290728 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290729 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30896 (p : Pattern) (selected : d290735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290726 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30894 q selected
    | true =>
      simp only [d290726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290727 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30895 q selected
    | true =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290732 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290733 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290734 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290735 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30897 (p : Pattern) (selected : d290739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30895 q selected
    | true =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290739 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30898 (p : Pattern) (selected : d290751 p = 1) : d295881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290657 q = 1) : d290657 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d290666 q = 1) : d290666 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d290698 q = 1) : d290698 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d290740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30896 q selected
    | true =>
      simp only [d290740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30897 q selected
  have h5 (q : Pattern) (selected : d290741 q = 1) : d295877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290741, d295877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290741, d295877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290747 q = 1) : d290747 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d290748 q = 1) : d295878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290748, d295878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290748, d295878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290749 q = 1) : d295879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290749, d295879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290749, d295879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290750 q = 1) : d295880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290750, d295880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290750, d295880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290751 q = 1) : d295881 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290751, d295881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290751, d295881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro30899 (p : Pattern) (selected : d290765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290726 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30894 q selected
    | true =>
      simp only [d290726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290727 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30895 q selected
    | true =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290732 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290733 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290734 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30900 (p : Pattern) (selected : d290766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30895 q selected
    | true =>
      simp only [d290730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290736 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290737 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290738 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290766 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30901 (p : Pattern) (selected : d290775 p = 1) : d295886 p = 1 := by
  have h0 (q : Pattern) (selected : d290657 q = 1) : d290657 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290666 q = 1) : d290666 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d290698 q = 1) : d290698 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d290740 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30896 q selected
    | true =>
      simp only [d290740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30897 q selected
  have h4 (q : Pattern) (selected : d290741 q = 1) : d295877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290741, d295877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290741, d295877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290747 q = 1) : d290747 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d290748 q = 1) : d295878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290748, d295878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290748, d295878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290749 q = 1) : d295879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290749, d295879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290749, d295879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290750 q = 1) : d295880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290750, d295880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290750, d295880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d290757 q = 1) : d290757 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d290762 q = 1) : d290762 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d290764 q = 1) : d290764 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d290767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30899 q selected
    | true =>
      simp only [d290767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30900 q selected
  have h13 (q : Pattern) (selected : d290768 q = 1) : d295882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290768, d295882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290768, d295882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290771 q = 1) : d290771 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d290772 q = 1) : d295883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290772, d295883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290772, d295883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290773 q = 1) : d295884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290773, d295884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290773, d295884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d290774 q = 1) : d295885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290774, d295885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290774, d295885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d290775 q = 1) : d295886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290775, d295886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290775, d295886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro30902 (p : Pattern) (selected : d290795 p = 1) : d295893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290764 q = 1) : d290764 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d290767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30899 q selected
    | true =>
      simp only [d290767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30900 q selected
  have h3 (q : Pattern) (selected : d290768 q = 1) : d295882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290768, d295882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290768, d295882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290771 q = 1) : d290771 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d290772 q = 1) : d295883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290772, d295883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290772, d295883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290793 q = 1) : d295891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290793, d295891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290793, d295891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290794 q = 1) : d295892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290794, d295892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290794, d295892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290795 q = 1) : d295893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290795, d295893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290795, d295893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30903 (p : Pattern) (selected : d290865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290855 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30890 q selected
  have h2 (q : Pattern) (selected : d290701 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30890 q selected
    | true =>
      simp only [d290701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d290856 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290702 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290857 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290858 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290859 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30891 q selected
  have h8 (q : Pattern) (selected : d290707 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d290707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30891 q selected
    | true =>
      simp only [d290707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290860 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290708 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d290708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d290708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d290861 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d290861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d290862 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d290862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d290862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d290863 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d290864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d290865 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30904 (p : Pattern) (selected : d290867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d153243 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
  have h2 (q : Pattern) (selected : d153152 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14126 q selected
    | true =>
      simp only [d153152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d153244 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d153244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d153153 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153245 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d153245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d153245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d153246 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d153246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d153246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290866 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d290866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290867 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d290867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30905 (p : Pattern) (selected : d290877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290868 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30903 q selected
    | true =>
      simp only [d290868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30904 q selected
  have h2 (q : Pattern) (selected : d290869 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290870 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290871 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30904 q selected
    | true =>
      simp only [d290871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290872 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290873 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290874 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d290876 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290877 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30906 (p : Pattern) (selected : d290881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290871 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d290871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30904 q selected
    | true =>
      simp only [d290871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290872 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d290872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290873 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d290873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d290875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290880 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d290880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290881 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d290881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30907 (p : Pattern) (selected : d290887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290878 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30905 q selected
    | true =>
      simp only [d290878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290879 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30906 q selected
    | true =>
      simp only [d290882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290884 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d290886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d290887 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30908 (p : Pattern) (selected : d290891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290882 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d290882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30906 q selected
    | true =>
      simp only [d290882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d290883 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d290883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290888 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d290888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d290888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d290889 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d290889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d290890 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d290890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d290891 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d290891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d290891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30909 (p : Pattern) (selected : d290903 p = 1) : d295903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290854 q = 1) : d290854 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d290892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30907 q selected
    | true =>
      simp only [d290892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30908 q selected
  have h3 (q : Pattern) (selected : d290893 q = 1) : d295899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290893, d295899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290893, d295899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290899 q = 1) : d290899 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d290900 q = 1) : d295900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290900, d295900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290900, d295900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290901 q = 1) : d295901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290901, d295901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290901, d295901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290902 q = 1) : d295902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290902, d295902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290902, d295902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d290903 q = 1) : d295903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290903, d295903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290903, d295903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30910 (p : Pattern) (selected : d290920 p = 1) : d295909 p = 1 := by
  have h0 (q : Pattern) (selected : d290649 q = 1) : d290649 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290776 q = 1) : d295887 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290776, d295887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30898 q selected
    | true =>
      simp only [d290776, d295887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30901 q selected
  have h2 (q : Pattern) (selected : d290789 q = 1) : d290789 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d290790 q = 1) : d295888 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290790, d295888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290790, d295888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d290791 q = 1) : d295889 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290791, d295889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d290791, d295889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290792 q = 1) : d295890 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290792, d295890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290792, d295890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d290796 q = 1) : d295894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290796, d295894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290796, d295894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30902 q selected
  have h8 (q : Pattern) (selected : d290798 q = 1) : d290798 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d290799 q = 1) : d295895 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290799, d295895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d290799, d295895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d290800 q = 1) : d295896 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290800, d295896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d290800, d295896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d290801 q = 1) : d295897 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290801, d295897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d290801, d295897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d290802 q = 1) : d295898 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290802, d295898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d290802, d295898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d290904 q = 1) : d295904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290904, d295904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d290904, d295904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30909 q selected
  have h14 (q : Pattern) (selected : d290915 q = 1) : d290915 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d290916 q = 1) : d295905 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290916, d295905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d290916, d295905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d290917 q = 1) : d295906 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290917, d295906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d290917, d295906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d290918 q = 1) : d295907 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290918, d295907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d290918, d295907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d290919 q = 1) : d295908 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290919, d295908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d290919, d295908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d290920 q = 1) : d295909 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290920, d295909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d290920, d295909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro30911 (p : Pattern) (selected : d290926 p = 1) : d295915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d290921 q = 1) : d295910 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290921, d295910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290921, d295910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30910 q selected
  have h2 (q : Pattern) (selected : d290922 q = 1) : d295911 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290922, d295911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290922, d295911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d290923 q = 1) : d295912 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290923, d295912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290923, d295912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d290924 q = 1) : d295913 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290924, d295913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290924, d295913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d290925 q = 1) : d295914 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290925, d295914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290925, d295914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d290926 q = 1) : d295915 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290926, d295915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290926, d295915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30912 (p : Pattern) (selected : d291053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro49 q selected
    | true =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1238 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d26229 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d26229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19183 q selected
    | true =>
      simp only [d26229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d26230 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d26230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d26230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291052 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291053 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro30913 (p : Pattern) (selected : d291059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291058 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d291059 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro30914 (p : Pattern) (selected : d291066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h2 (q : Pattern) (selected : d1271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291065 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291066 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30915 (p : Pattern) (selected : d291072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291054 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30912 q selected
    | true =>
      simp only [d291054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291055 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291056 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291057 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291060 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30913 q selected
    | true =>
      simp only [d291060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291061 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291062 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291063 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291064 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
    | true =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291069 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291070 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291071 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291072 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30916 (p : Pattern) (selected : d291074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25812 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19156 q selected
    | true =>
      simp only [d25812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d25813 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291073 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291074 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro30917 (p : Pattern) (selected : d291081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291075 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30916 q selected
    | true =>
      simp only [d291075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291076 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291077 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291078 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
    | true =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291069 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291070 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291079 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291080 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291081 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30918 (p : Pattern) (selected : d291085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
    | true =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291069 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291070 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291080 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291085 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30919 (p : Pattern) (selected : d291092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291082 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30915 q selected
    | true =>
      simp only [d291082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30917 q selected
  have h2 (q : Pattern) (selected : d291083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30917 q selected
    | true =>
      simp only [d291086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30918 q selected
  have h5 (q : Pattern) (selected : d291087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291089 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291090 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291091 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291092 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30920 (p : Pattern) (selected : d291096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30917 q selected
    | true =>
      simp only [d291086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30918 q selected
  have h2 (q : Pattern) (selected : d291087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291090 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291095 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291096 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30921 (p : Pattern) (selected : d291102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291093 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30919 q selected
    | true =>
      simp only [d291093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291094 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30920 q selected
    | true =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291099 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291102 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30922 (p : Pattern) (selected : d291106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30920 q selected
    | true =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291104 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291105 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291106 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30923 (p : Pattern) (selected : d291118 p = 1) : d295922 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291010 q = 1) : d291010 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291019 q = 1) : d291019 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291051 q = 1) : d291051 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d291107 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30921 q selected
    | true =>
      simp only [d291107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30922 q selected
  have h5 (q : Pattern) (selected : d291108 q = 1) : d295918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291108, d295918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291108, d295918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291114 q = 1) : d291114 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d291115 q = 1) : d295919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291115, d295919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291115, d295919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291116 q = 1) : d295920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291116, d295920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291116, d295920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291117 q = 1) : d295921 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291117, d295921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291117, d295921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291118 q = 1) : d295922 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291118, d295922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291118, d295922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro30924 (p : Pattern) (selected : d291132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291093 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30919 q selected
    | true =>
      simp only [d291093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291094 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30920 q selected
    | true =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291099 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291101 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30925 (p : Pattern) (selected : d291133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291097 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30920 q selected
    | true =>
      simp only [d291097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291098 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291104 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291105 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30926 (p : Pattern) (selected : d291142 p = 1) : d295927 p = 1 := by
  have h0 (q : Pattern) (selected : d291010 q = 1) : d291010 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291019 q = 1) : d291019 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291051 q = 1) : d291051 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291107 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30921 q selected
    | true =>
      simp only [d291107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30922 q selected
  have h4 (q : Pattern) (selected : d291108 q = 1) : d295918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291108, d295918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291108, d295918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291114 q = 1) : d291114 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d291115 q = 1) : d295919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291115, d295919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291115, d295919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291116 q = 1) : d295920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291116, d295920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291116, d295920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291117 q = 1) : d295921 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291117, d295921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291117, d295921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291124 q = 1) : d291124 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d291129 q = 1) : d291129 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d291131 q = 1) : d291131 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d291134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30924 q selected
    | true =>
      simp only [d291134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30925 q selected
  have h13 (q : Pattern) (selected : d291135 q = 1) : d295923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291135, d295923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291135, d295923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291138 q = 1) : d291138 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d291139 q = 1) : d295924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291139, d295924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291139, d295924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291140 q = 1) : d295925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291140, d295925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291140, d295925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291141 q = 1) : d295926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291141, d295926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291141, d295926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d291142 q = 1) : d295927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291142, d295927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291142, d295927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro30927 (p : Pattern) (selected : d291162 p = 1) : d295934 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291131 q = 1) : d291131 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30924 q selected
    | true =>
      simp only [d291134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30925 q selected
  have h3 (q : Pattern) (selected : d291135 q = 1) : d295923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291135, d295923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291135, d295923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291138 q = 1) : d291138 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291139 q = 1) : d295924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291139, d295924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291139, d295924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291160 q = 1) : d295932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291160, d295932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291160, d295932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291161 q = 1) : d295933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291161, d295933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291161, d295933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291162 q = 1) : d295934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291162, d295934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291162, d295934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30928 (p : Pattern) (selected : d291255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291241 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30912 q selected
  have h2 (q : Pattern) (selected : d291054 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30912 q selected
    | true =>
      simp only [d291054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291242 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291055 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291243 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291244 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30913 q selected
  have h8 (q : Pattern) (selected : d291060 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30913 q selected
    | true =>
      simp only [d291060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291061 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291250 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
  have h15 (q : Pattern) (selected : d291067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
    | true =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291251 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291252 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291253 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291254 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291255 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30929 (p : Pattern) (selected : d291262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291256 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30916 q selected
  have h2 (q : Pattern) (selected : d291075 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30916 q selected
    | true =>
      simp only [d291075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291076 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291258 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291259 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291250 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
  have h8 (q : Pattern) (selected : d291067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
    | true =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291251 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291252 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291253 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291260 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291261 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291262 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30930 (p : Pattern) (selected : d291266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291250 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
  have h2 (q : Pattern) (selected : d291067 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30914 q selected
    | true =>
      simp only [d291067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291251 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291068 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291252 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291253 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291261 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291266 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30931 (p : Pattern) (selected : d291273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291263 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30928 q selected
    | true =>
      simp only [d291263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30929 q selected
  have h2 (q : Pattern) (selected : d291264 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291265 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291267 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30929 q selected
    | true =>
      simp only [d291267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30930 q selected
  have h5 (q : Pattern) (selected : d291268 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291269 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291270 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291271 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291273 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30932 (p : Pattern) (selected : d291277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291267 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30929 q selected
    | true =>
      simp only [d291267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30930 q selected
  have h2 (q : Pattern) (selected : d291268 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291269 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291271 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291276 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291277 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30933 (p : Pattern) (selected : d291283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30931 q selected
    | true =>
      simp only [d291274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30932 q selected
    | true =>
      simp only [d291278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291280 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291281 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291282 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291283 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30934 (p : Pattern) (selected : d291287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291278 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30932 q selected
    | true =>
      simp only [d291278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291279 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291284 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291285 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291287 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30935 (p : Pattern) (selected : d291299 p = 1) : d295944 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291240 q = 1) : d291240 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291288 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30933 q selected
    | true =>
      simp only [d291288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30934 q selected
  have h3 (q : Pattern) (selected : d291289 q = 1) : d295940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291289, d295940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291289, d295940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291295 q = 1) : d291295 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291296 q = 1) : d295941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291296, d295941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291296, d295941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291297 q = 1) : d295942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291297, d295942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291297, d295942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291298 q = 1) : d295943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291298, d295943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291298, d295943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291299 q = 1) : d295944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291299, d295944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291299, d295944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30936 (p : Pattern) (selected : d291316 p = 1) : d295950 p = 1 := by
  have h0 (q : Pattern) (selected : d291002 q = 1) : d291002 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291143 q = 1) : d295928 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291143, d295928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30923 q selected
    | true =>
      simp only [d291143, d295928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30926 q selected
  have h2 (q : Pattern) (selected : d291156 q = 1) : d291156 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291157 q = 1) : d295929 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291157, d295929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291157, d295929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291158 q = 1) : d295930 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291158, d295930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291158, d295930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291159 q = 1) : d295931 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291159, d295931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291159, d295931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291163 q = 1) : d295935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291163, d295935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291163, d295935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30927 q selected
  have h8 (q : Pattern) (selected : d291165 q = 1) : d291165 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d291166 q = 1) : d295936 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291166, d295936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291166, d295936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291167 q = 1) : d295937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291167, d295937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291167, d295937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d291168 q = 1) : d295938 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291168, d295938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291168, d295938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d291169 q = 1) : d295939 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291169, d295939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291169, d295939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291300 q = 1) : d295945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291300, d295945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291300, d295945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30935 q selected
  have h14 (q : Pattern) (selected : d291311 q = 1) : d291311 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d291312 q = 1) : d295946 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291312, d295946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291312, d295946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291313 q = 1) : d295947 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291313, d295947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291313, d295947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d291314 q = 1) : d295948 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291314, d295948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291314, d295948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d291315 q = 1) : d295949 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291315, d295949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d291315, d295949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d291316 q = 1) : d295950 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d291316, d295950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291316, d295950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro30937 (p : Pattern) (selected : d291322 p = 1) : d295956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291317 q = 1) : d295951 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d291317, d295951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291317, d295951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30936 q selected
  have h2 (q : Pattern) (selected : d291318 q = 1) : d295952 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d291318, d295952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291318, d295952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291319 q = 1) : d295953 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d291319, d295953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291319, d295953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291320 q = 1) : d295954 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d291320, d295954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291320, d295954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291321 q = 1) : d295955 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d291321, d295955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291321, d295955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291322 q = 1) : d295956 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d291322, d295956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291322, d295956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30938 (p : Pattern) (selected : d291443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro106 q selected
    | true =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro107 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h3 (q : Pattern) (selected : d1697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30939 (p : Pattern) (selected : d291449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h3 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291448 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291449 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30940 (p : Pattern) (selected : d291456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1746 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
  have h2 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h3 (q : Pattern) (selected : d1747 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
    | true =>
      simp only [d10249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291455 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291456 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30941 (p : Pattern) (selected : d291462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291444 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30938 q selected
    | true =>
      simp only [d291444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291445 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291446 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291447 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30939 q selected
    | true =>
      simp only [d291450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291452 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291453 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291454 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
    | true =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291460 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291461 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291462 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30942 (p : Pattern) (selected : d291464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h3 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d26229 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d26229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19183 q selected
    | true =>
      simp only [d26229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d26230 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d26230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d26230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d291463 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291464 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro30943 (p : Pattern) (selected : d291471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291465 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30942 q selected
    | true =>
      simp only [d291465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291466 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291467 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291468 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
    | true =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291460 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291469 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291470 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291471 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30944 (p : Pattern) (selected : d291475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
    | true =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291460 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291470 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291475 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30945 (p : Pattern) (selected : d291482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291472 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30941 q selected
    | true =>
      simp only [d291472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30943 q selected
  have h2 (q : Pattern) (selected : d291473 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291474 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291476 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30943 q selected
    | true =>
      simp only [d291476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30944 q selected
  have h5 (q : Pattern) (selected : d291477 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291478 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291479 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291482 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30946 (p : Pattern) (selected : d291486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291476 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30943 q selected
    | true =>
      simp only [d291476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30944 q selected
  have h2 (q : Pattern) (selected : d291477 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291478 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291485 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291486 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30947 (p : Pattern) (selected : d291492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30945 q selected
    | true =>
      simp only [d291483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30946 q selected
    | true =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291491 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291492 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30948 (p : Pattern) (selected : d291496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30946 q selected
    | true =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291494 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291495 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291496 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30949 (p : Pattern) (selected : d291525 p = 1) : d295964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291407 q = 1) : d291407 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291416 q = 1) : d291416 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291441 q = 1) : d291441 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d291497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30947 q selected
    | true =>
      simp only [d291497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30948 q selected
  have h5 (q : Pattern) (selected : d291498 q = 1) : d295960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291498, d295960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291498, d295960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291521 q = 1) : d291521 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d291522 q = 1) : d295961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291522, d295961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291522, d295961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291523 q = 1) : d295962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291523, d295962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291523, d295962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291524 q = 1) : d295963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291524, d295963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291524, d295963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291525 q = 1) : d295964 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291525, d295964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291525, d295964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro30950 (p : Pattern) (selected : d291539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291483 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30945 q selected
    | true =>
      simp only [d291483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291484 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30946 q selected
    | true =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291489 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291490 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291491 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291539 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30951 (p : Pattern) (selected : d291540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291487 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30946 q selected
    | true =>
      simp only [d291487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291488 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291493 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291494 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291495 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291540 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30952 (p : Pattern) (selected : d291549 p = 1) : d295969 p = 1 := by
  have h0 (q : Pattern) (selected : d291407 q = 1) : d291407 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291416 q = 1) : d291416 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291441 q = 1) : d291441 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291497 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30947 q selected
    | true =>
      simp only [d291497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30948 q selected
  have h4 (q : Pattern) (selected : d291498 q = 1) : d295960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291498, d295960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291498, d295960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291521 q = 1) : d291521 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d291522 q = 1) : d295961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291522, d295961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291522, d295961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291523 q = 1) : d295962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291523, d295962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291523, d295962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291524 q = 1) : d295963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291524, d295963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291524, d295963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291531 q = 1) : d291531 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d291536 q = 1) : d291536 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d291538 q = 1) : d291538 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d291541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30950 q selected
    | true =>
      simp only [d291541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30951 q selected
  have h13 (q : Pattern) (selected : d291542 q = 1) : d295965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291542, d295965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291542, d295965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291545 q = 1) : d291545 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d291546 q = 1) : d295966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291546, d295966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291546, d295966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291547 q = 1) : d295967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291547, d295967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291547, d295967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291548 q = 1) : d295968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291548, d295968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291548, d295968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d291549 q = 1) : d295969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291549, d295969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291549, d295969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro30953 (p : Pattern) (selected : d291569 p = 1) : d295976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291538 q = 1) : d291538 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30950 q selected
    | true =>
      simp only [d291541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30951 q selected
  have h3 (q : Pattern) (selected : d291542 q = 1) : d295965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291542, d295965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291542, d295965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291545 q = 1) : d291545 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291546 q = 1) : d295966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291546, d295966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291546, d295966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291567 q = 1) : d295974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291567, d295974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291567, d295974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291568 q = 1) : d295975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291568, d295975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291568, d295975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291569 q = 1) : d295976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291569, d295976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291569, d295976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30954 (p : Pattern) (selected : d291657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291643 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30938 q selected
  have h2 (q : Pattern) (selected : d291444 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30938 q selected
    | true =>
      simp only [d291444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291644 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291445 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291645 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291646 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291647 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30939 q selected
  have h8 (q : Pattern) (selected : d291450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30939 q selected
    | true =>
      simp only [d291450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291648 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291649 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291650 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291651 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291652 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
  have h15 (q : Pattern) (selected : d291457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
    | true =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d291653 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d291653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d291654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d291655 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d291655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d291656 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d291657 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30955 (p : Pattern) (selected : d291664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291658 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30942 q selected
  have h2 (q : Pattern) (selected : d291465 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30942 q selected
    | true =>
      simp only [d291465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291659 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291466 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291660 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291661 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291652 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
  have h8 (q : Pattern) (selected : d291457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
    | true =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291653 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d291655 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d291662 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291663 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d291664 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30956 (p : Pattern) (selected : d291668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291652 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
  have h2 (q : Pattern) (selected : d291457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30940 q selected
    | true =>
      simp only [d291457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291653 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291655 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291663 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291668 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30957 (p : Pattern) (selected : d291675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291665 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30954 q selected
    | true =>
      simp only [d291665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30955 q selected
  have h2 (q : Pattern) (selected : d291666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291667 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291669 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30955 q selected
    | true =>
      simp only [d291669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30956 q selected
  have h5 (q : Pattern) (selected : d291670 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291671 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291673 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291674 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291675 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30958 (p : Pattern) (selected : d291679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291669 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30955 q selected
    | true =>
      simp only [d291669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30956 q selected
  have h2 (q : Pattern) (selected : d291670 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291671 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291673 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291678 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291679 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30959 (p : Pattern) (selected : d291685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291676 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30957 q selected
    | true =>
      simp only [d291676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291677 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30958 q selected
    | true =>
      simp only [d291680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30960 (p : Pattern) (selected : d291689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30958 q selected
    | true =>
      simp only [d291680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291686 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291687 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291688 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291689 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30961 (p : Pattern) (selected : d291716 p = 1) : d295986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291642 q = 1) : d291642 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291690 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30959 q selected
    | true =>
      simp only [d291690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30960 q selected
  have h3 (q : Pattern) (selected : d291691 q = 1) : d295982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291691, d295982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291691, d295982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291712 q = 1) : d291712 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291713 q = 1) : d295983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291713, d295983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291713, d295983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291714 q = 1) : d295984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291714, d295984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291714, d295984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291715 q = 1) : d295985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291715, d295985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291715, d295985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291716 q = 1) : d295986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291716, d295986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291716, d295986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30962 (p : Pattern) (selected : d291733 p = 1) : d295992 p = 1 := by
  have h0 (q : Pattern) (selected : d291399 q = 1) : d291399 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291550 q = 1) : d295970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291550, d295970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30949 q selected
    | true =>
      simp only [d291550, d295970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30952 q selected
  have h2 (q : Pattern) (selected : d291563 q = 1) : d291563 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291564 q = 1) : d295971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291564, d295971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291564, d295971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291565 q = 1) : d295972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291565, d295972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291565, d295972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291566 q = 1) : d295973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291566, d295973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291566, d295973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291570 q = 1) : d295977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291570, d295977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291570, d295977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30953 q selected
  have h8 (q : Pattern) (selected : d291572 q = 1) : d291572 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d291573 q = 1) : d295978 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291573, d295978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291573, d295978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291574 q = 1) : d295979 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291574, d295979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291574, d295979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d291575 q = 1) : d295980 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291575, d295980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291575, d295980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d291576 q = 1) : d295981 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291576, d295981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291576, d295981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291717 q = 1) : d295987 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291717, d295987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291717, d295987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30961 q selected
  have h14 (q : Pattern) (selected : d291728 q = 1) : d291728 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d291729 q = 1) : d295988 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291729, d295988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291729, d295988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291730 q = 1) : d295989 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291730, d295989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291730, d295989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d291731 q = 1) : d295990 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291731, d295990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d291731, d295990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d291732 q = 1) : d295991 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291732, d295991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d291732, d295991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d291733 q = 1) : d295992 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d291733, d295992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291733, d295992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro30963 (p : Pattern) (selected : d291739 p = 1) : d295998 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291734 q = 1) : d295993 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d291734, d295993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291734, d295993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30962 q selected
  have h2 (q : Pattern) (selected : d291735 q = 1) : d295994 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d291735, d295994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291735, d295994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291736 q = 1) : d295995 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d291736, d295995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291736, d295995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291737 q = 1) : d295996 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d291737, d295996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291737, d295996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291738 q = 1) : d295997 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d291738, d295997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291738, d295997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291739 q = 1) : d295998 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d291739, d295998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291739, d295998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30964 (p : Pattern) (selected : d291837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro144 q selected
    | true =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro145 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h3 (q : Pattern) (selected : d2191 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291836 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d291837 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30965 (p : Pattern) (selected : d291844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2224 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
  have h2 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h3 (q : Pattern) (selected : d2225 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10514 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
    | true =>
      simp only [d10514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10515 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
    | true =>
      simp only [d10515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10516 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291843 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d291843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291844 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d291844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30966 (p : Pattern) (selected : d291850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14218 q selected
    | true =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d154624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154625 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154626 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291838 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30964 q selected
    | true =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291839 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291840 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291841 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291842 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291845 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
    | true =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d291847 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d291848 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d291848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d291849 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d291850 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30967 (p : Pattern) (selected : d291852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291838 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30964 q selected
    | true =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291839 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291840 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291841 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291845 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
    | true =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291847 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291848 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291849 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d291852 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro30968 (p : Pattern) (selected : d291856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291845 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
    | true =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291847 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d291847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291848 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d291848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d291851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291856 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d291856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30969 (p : Pattern) (selected : d291863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30966 q selected
    | true =>
      simp only [d291853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30967 q selected
  have h2 (q : Pattern) (selected : d291854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291857 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30967 q selected
    | true =>
      simp only [d291857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30968 q selected
  have h5 (q : Pattern) (selected : d291858 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291859 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291860 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30970 (p : Pattern) (selected : d291867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291857 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d291857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30967 q selected
    | true =>
      simp only [d291857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30968 q selected
  have h2 (q : Pattern) (selected : d291858 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d291858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291859 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d291859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d291861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291866 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d291866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291867 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d291867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30971 (p : Pattern) (selected : d291873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30969 q selected
    | true =>
      simp only [d291864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291868 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30970 q selected
    | true =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291869 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291871 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291872 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291873 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30972 (p : Pattern) (selected : d291877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291868 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30970 q selected
    | true =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291869 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291877 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30973 (p : Pattern) (selected : d291898 p = 1) : d296007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291812 q = 1) : d291812 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291821 q = 1) : d291821 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291835 q = 1) : d291835 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d291878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30971 q selected
    | true =>
      simp only [d291878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30972 q selected
  have h5 (q : Pattern) (selected : d291879 q = 1) : d296003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291879, d296003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291879, d296003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291894 q = 1) : d291894 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d291895 q = 1) : d296004 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291895, d296004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291895, d296004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291896 q = 1) : d296005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291896, d296005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291896, d296005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291897 q = 1) : d296006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291897, d296006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291897, d296006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291898 q = 1) : d296007 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291898, d296007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291898, d296007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro30974 (p : Pattern) (selected : d291912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30969 q selected
    | true =>
      simp only [d291864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291868 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30970 q selected
    | true =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291869 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291871 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291872 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d291912 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30975 (p : Pattern) (selected : d291913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291868 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30970 q selected
    | true =>
      simp only [d291868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d291869 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d291874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d291874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d291875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d291875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d291876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d291876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d291913 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d291913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d291913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30976 (p : Pattern) (selected : d291922 p = 1) : d296012 p = 1 := by
  have h0 (q : Pattern) (selected : d291812 q = 1) : d291812 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291821 q = 1) : d291821 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291835 q = 1) : d291835 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30971 q selected
    | true =>
      simp only [d291878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30972 q selected
  have h4 (q : Pattern) (selected : d291879 q = 1) : d296003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291879, d296003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291879, d296003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d291894 q = 1) : d291894 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d291895 q = 1) : d296004 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291895, d296004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291895, d296004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291896 q = 1) : d296005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291896, d296005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291896, d296005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291897 q = 1) : d296006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291897, d296006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291897, d296006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291904 q = 1) : d291904 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d291909 q = 1) : d291909 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d291911 q = 1) : d291911 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d291914 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30974 q selected
    | true =>
      simp only [d291914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30975 q selected
  have h13 (q : Pattern) (selected : d291915 q = 1) : d296008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291915, d296008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d291915, d296008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d291918 q = 1) : d291918 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d291919 q = 1) : d296009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291919, d296009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d291919, d296009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d291920 q = 1) : d296010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291920, d296010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291920, d296010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291921 q = 1) : d296011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291921, d296011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291921, d296011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d291922 q = 1) : d296012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291922, d296012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291922, d296012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro30977 (p : Pattern) (selected : d291942 p = 1) : d296019 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291911 q = 1) : d291911 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d291914 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d291914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30974 q selected
    | true =>
      simp only [d291914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30975 q selected
  have h3 (q : Pattern) (selected : d291915 q = 1) : d296008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d291915, d296008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291915, d296008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291918 q = 1) : d291918 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291919 q = 1) : d296009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d291919, d296009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291919, d296009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291940 q = 1) : d296017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d291940, d296017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291940, d296017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291941 q = 1) : d296018 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d291941, d296018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291941, d296018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d291942 q = 1) : d296019 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291942, d296019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291942, d296019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30978 (p : Pattern) (selected : d292008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d154815 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d154815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14218 q selected
  have h2 (q : Pattern) (selected : d154623 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14218 q selected
    | true =>
      simp only [d154623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d154816 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d154816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d154624 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d154624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d154817 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d154817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d154817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154818 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d154818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d291998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30964 q selected
  have h8 (q : Pattern) (selected : d291838 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30964 q selected
    | true =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d291999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291839 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d292000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d292000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d292001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d292001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d292002 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d292003 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
  have h15 (q : Pattern) (selected : d291845 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
    | true =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d292004 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d292004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d291846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d292005 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d292005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d292006 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d292006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d292007 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d292007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d292008 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d292008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro30979 (p : Pattern) (selected : d292010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291998 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30964 q selected
  have h2 (q : Pattern) (selected : d291838 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30964 q selected
    | true =>
      simp only [d291838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d291999 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291839 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292000 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292001 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d292003 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
  have h8 (q : Pattern) (selected : d291845 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
    | true =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d292004 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d292005 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d292005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d292006 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d292006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d292007 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d292009 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d292009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d292010 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d292010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro30980 (p : Pattern) (selected : d292014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292003 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
  have h2 (q : Pattern) (selected : d291845 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30965 q selected
    | true =>
      simp only [d291845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292004 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291846 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d291846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292005 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292006 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d292009 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d292014 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30981 (p : Pattern) (selected : d292021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292011 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30978 q selected
    | true =>
      simp only [d292011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30979 q selected
  have h2 (q : Pattern) (selected : d292012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30979 q selected
    | true =>
      simp only [d292015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30980 q selected
  have h5 (q : Pattern) (selected : d292016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d292018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d292019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d292020 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d292021 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d292021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro30982 (p : Pattern) (selected : d292025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30979 q selected
    | true =>
      simp only [d292015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30980 q selected
  have h2 (q : Pattern) (selected : d292016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292019 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292024 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292025 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30983 (p : Pattern) (selected : d292031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292022 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30981 q selected
    | true =>
      simp only [d292022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292023 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292026 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30982 q selected
    | true =>
      simp only [d292026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292027 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d292028 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292029 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d292030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d292030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d292031 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d292031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro30984 (p : Pattern) (selected : d292035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292026 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30982 q selected
    | true =>
      simp only [d292026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292027 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30985 (p : Pattern) (selected : d292056 p = 1) : d296029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291997 q = 1) : d291997 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d292036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30983 q selected
    | true =>
      simp only [d292036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30984 q selected
  have h3 (q : Pattern) (selected : d292037 q = 1) : d296025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292037, d296025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292037, d296025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292052 q = 1) : d292052 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d292053 q = 1) : d296026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292053, d296026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292053, d296026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292054 q = 1) : d296027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292054, d296027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292054, d296027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d292055 q = 1) : d296028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292055, d296028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292055, d296028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d292056 q = 1) : d296029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292056, d296029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292056, d296029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro30986 (p : Pattern) (selected : d292073 p = 1) : d296035 p = 1 := by
  have h0 (q : Pattern) (selected : d291804 q = 1) : d291804 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d291923 q = 1) : d296013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291923, d296013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30973 q selected
    | true =>
      simp only [d291923, d296013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30976 q selected
  have h2 (q : Pattern) (selected : d291936 q = 1) : d291936 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d291937 q = 1) : d296014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291937, d296014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291937, d296014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d291938 q = 1) : d296015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291938, d296015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291938, d296015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291939 q = 1) : d296016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291939, d296016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d291939, d296016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291943 q = 1) : d296020 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d291943, d296020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d291943, d296020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30977 q selected
  have h8 (q : Pattern) (selected : d291945 q = 1) : d291945 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d291946 q = 1) : d296021 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d291946, d296021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d291946, d296021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291947 q = 1) : d296022 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d291947, d296022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d291947, d296022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d291948 q = 1) : d296023 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d291948, d296023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d291948, d296023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d291949 q = 1) : d296024 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d291949, d296024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291949, d296024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d292057 q = 1) : d296030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292057, d296030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292057, d296030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30985 q selected
  have h14 (q : Pattern) (selected : d292068 q = 1) : d292068 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d292069 q = 1) : d296031 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292069, d296031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d292069, d296031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d292070 q = 1) : d296032 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292070, d296032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d292070, d296032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d292071 q = 1) : d296033 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292071, d296033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d292071, d296033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d292072 q = 1) : d296034 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292072, d296034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d292072, d296034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d292073 q = 1) : d296035 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d292073, d296035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d292073, d296035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro30987 (p : Pattern) (selected : d292079 p = 1) : d296041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292074 q = 1) : d296036 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d292074, d296036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292074, d296036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30986 q selected
  have h2 (q : Pattern) (selected : d292075 q = 1) : d296037 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d292075, d296037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292075, d296037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d292076 q = 1) : d296038 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d292076, d296038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292076, d296038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d292077 q = 1) : d296039 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d292077, d296039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292077, d296039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d292078 q = 1) : d296040 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d292078, d296040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292078, d296040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d292079 q = 1) : d296041 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d292079, d296041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d292079, d296041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro30988 (p : Pattern) (selected : d292085 p = 1) : d296047 p = 1 := by
  have h0 (q : Pattern) (selected : d290602 q = 1) : d295876 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290602, d295876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14125 q selected
    | true =>
      simp only [d290602, d295876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30889 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d290927 q = 1) : d295916 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290927, d295916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d290927, d295916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30911 q selected
  have h3 (q : Pattern) (selected : d290928 q = 1) : d295917 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290928, d295917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d290928, d295917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d291323 q = 1) : d295957 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d291323, d295957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291323, d295957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30937 q selected
  have h5 (q : Pattern) (selected : d291324 q = 1) : d295958 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d291324, d295958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291324, d295958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d291325 q = 1) : d295959 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d291325, d295959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d291325, d295959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d291740 q = 1) : d295999 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d291740, d295999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291740, d295999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30963 q selected
  have h8 (q : Pattern) (selected : d291741 q = 1) : d296000 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d291741, d296000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291741, d296000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d291742 q = 1) : d296001 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d291742, d296001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d291742, d296001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d291743 q = 1) : d296002 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d291743, d296002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d291743, d296002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d292080 q = 1) : d296042 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d292080, d296042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292080, d296042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30987 q selected
  have h12 (q : Pattern) (selected : d292081 q = 1) : d296043 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d292081, d296043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292081, d296043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d292082 q = 1) : d296044 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d292082, d296044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292082, d296044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d292083 q = 1) : d296045 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d292083, d296045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292083, d296045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d292084 q = 1) : d296046 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d292084, d296046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d292084, d296046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d292085 q = 1) : d296047 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d292085, d296047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d292085, d296047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro30989 (p : Pattern) (selected : d292091 p = 1) : d296053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292086 q = 1) : d296048 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d292086, d296048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30988 q selected
    | true =>
      simp only [d292086, d296048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292087 q = 1) : d296049 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d292087, d296049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292087, d296049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292088 q = 1) : d296050 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d292088, d296050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292088, d296050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292089 q = 1) : d296051 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d292089, d296051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292089, d296051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292090 q = 1) : d296052 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d292090, d296052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292090, d296052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292091 q = 1) : d296053 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d292091, d296053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292091, d296053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30990 (p : Pattern) (selected : d292097 p = 1) : d296059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292092 q = 1) : d296054 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d292092, d296054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30989 q selected
    | true =>
      simp only [d292092, d296054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292093 q = 1) : d296055 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d292093, d296055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292093, d296055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292094 q = 1) : d296056 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d292094, d296056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292094, d296056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292095 q = 1) : d296057 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d292095, d296057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292095, d296057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292096 q = 1) : d296058 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d292096, d296058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292096, d296058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292097 q = 1) : d296059 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d292097, d296059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292097, d296059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30991 (p : Pattern) (selected : d292103 p = 1) : d296065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292098 q = 1) : d296060 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d292098, d296060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30990 q selected
    | true =>
      simp only [d292098, d296060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292099 q = 1) : d296061 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d292099, d296061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292099, d296061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292100 q = 1) : d296062 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d292100, d296062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292100, d296062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292101 q = 1) : d296063 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d292101, d296063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292101, d296063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292102 q = 1) : d296064 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d292102, d296064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292102, d296064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292103 q = 1) : d296065 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d292103, d296065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292103, d296065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30992 (p : Pattern) (selected : d292109 p = 1) : d296071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292104 q = 1) : d296066 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d292104, d296066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30991 q selected
    | true =>
      simp only [d292104, d296066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292105 q = 1) : d296067 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d292105, d296067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292105, d296067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292106 q = 1) : d296068 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d292106, d296068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292106, d296068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292107 q = 1) : d296069 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d292107, d296069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292107, d296069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292108 q = 1) : d296070 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d292108, d296070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292108, d296070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292109 q = 1) : d296071 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d292109, d296071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292109, d296071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30993 (p : Pattern) (selected : d292115 p = 1) : d296077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292110 q = 1) : d296072 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d292110, d296072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30992 q selected
    | true =>
      simp only [d292110, d296072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292111 q = 1) : d296073 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d292111, d296073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292111, d296073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292112 q = 1) : d296074 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d292112, d296074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292112, d296074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292113 q = 1) : d296075 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d292113, d296075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292113, d296075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292114 q = 1) : d296076 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d292114, d296076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292114, d296076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292115 q = 1) : d296077 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d292115, d296077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292115, d296077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30994 (p : Pattern) (selected : d292121 p = 1) : d296083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292116 q = 1) : d296078 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d292116, d296078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30993 q selected
    | true =>
      simp only [d292116, d296078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292117 q = 1) : d296079 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d292117, d296079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292117, d296079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292118 q = 1) : d296080 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d292118, d296080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292118, d296080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292119 q = 1) : d296081 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d292119, d296081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292119, d296081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292120 q = 1) : d296082 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d292120, d296082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292120, d296082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292121 q = 1) : d296083 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d292121, d296083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292121, d296083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30995 (p : Pattern) (selected : d292127 p = 1) : d296089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d292122 q = 1) : d296084 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d292122, d296084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30994 q selected
    | true =>
      simp only [d292122, d296084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d292123 q = 1) : d296085 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d292123, d296085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d292123, d296085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292124 q = 1) : d296086 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d292124, d296086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d292124, d296086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d292125 q = 1) : d296087 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d292125, d296087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d292125, d296087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d292126 q = 1) : d296088 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d292126, d296088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d292126, d296088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d292127 q = 1) : d296089 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d292127, d296089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d292127, d296089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30996 (p : Pattern) (selected : d300402 p = 0) : d302509 p = 1 := by
  have h0 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d300402 q = 0) : d302509 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d300402, d302509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300402, d302509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro30997 (p : Pattern) (selected : d300408 p = 0) : d302515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d300403 q = 0) : d302510 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d300403, d302510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30996 q selected
    | true =>
      simp only [d300403, d302510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300404 q = 0) : d302511 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d300404, d302511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300404, d302511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300405 q = 0) : d302512 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d300405, d302512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d300405, d302512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300406 q = 0) : d302513 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d300406, d302513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300406, d302513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300407 q = 0) : d302514 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d300407, d302514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300407, d302514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300408 q = 0) : d302515 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d300408, d302515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300408, d302515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30998 (p : Pattern) (selected : d300414 p = 0) : d302521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d300409 q = 0) : d302516 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d300409, d302516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30997 q selected
    | true =>
      simp only [d300409, d302516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300410 q = 0) : d302517 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d300410, d302517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d300410, d302517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d300411 q = 0) : d302518 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d300411, d302518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300411, d302518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300412 q = 0) : d302519 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d300412, d302519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300412, d302519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300413 q = 0) : d302520 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d300413, d302520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300413, d302520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300414 q = 0) : d302521 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d300414, d302521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300414, d302521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro30999 (p : Pattern) (selected : d300420 p = 0) : d302527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d300415 q = 0) : d302522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d300415, d302522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30998 q selected
    | true =>
      simp only [d300415, d302522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d300416 q = 0) : d302523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d300416, d302523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300416, d302523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d300417 q = 0) : d302524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d300417, d302524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300417, d302524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d300418 q = 0) : d302525 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d300418, d302525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d300418, d302525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d300419 q = 0) : d302526 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d300419, d302526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d300419, d302526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d300420 q = 0) : d302527 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d300420, d302527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d300420, d302527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
