import NetHack.Soko22Hazard87.EqIntroBlocks0018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro4750 (p : Pattern) (selected : d7754 p = 0) : d84119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 0) : d84097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7753 q = 0) : d84118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7754 q = 0) : d84119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d84119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7754, d84119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4751 (p : Pattern) (selected : d7761 p = 0) : d84126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7759 q = 0) : d84124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7760 q = 0) : d84125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7761 q = 0) : d84126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d84126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7761, d84126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4752 (p : Pattern) (selected : d7766 p = 0) : d84131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1216 q = 0) : d52797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro408 q selected
    | true =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
  have h2 (q : Pattern) (selected : d1217 q = 0) : d52798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1218 q = 0) : d52799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1129 q = 0) : d52710 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h5 (q : Pattern) (selected : d1130 q = 0) : d52711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1131 q = 0) : d52712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1219 q = 0) : d52800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d52800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1219, d52800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7765 q = 0) : d84130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7765, d84130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7765, d84130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7766 q = 0) : d84131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7766, d84131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7766, d84131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4753 (p : Pattern) (selected : d7772 p = 0) : d84137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7767 q = 0) : d84132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4752 q selected
    | true =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7768 q = 0) : d84133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7769 q = 0) : d84134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d84134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7769, d84134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7770 q = 0) : d84135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d84135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7770, d84135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7771 q = 0) : d84136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d84136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7771, d84136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7772 q = 0) : d84137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, d84137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7772, d84137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4754 (p : Pattern) (selected : d7775 p = 0) : d84093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1284 q = 0) : d52710 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1284, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro418 q selected
    | true =>
      simp only [d1284, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro419 q selected
  have h2 (q : Pattern) (selected : d1285 q = 0) : d52711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1285, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1285, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1286 q = 0) : d52712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1286, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1286, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1297 q = 0) : d52723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1297, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro419 q selected
    | true =>
      simp only [d1297, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro421 q selected
  have h5 (q : Pattern) (selected : d1298 q = 0) : d52724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1298, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1298, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1299 q = 0) : d52725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1299, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1299, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1300 q = 0) : d52726 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1300, d52726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1300, d52726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7774 q = 0) : d84092 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7774, d84092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7774, d84092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7775 q = 0) : d84093 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7775, d84093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7775, d84093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4755 (p : Pattern) (selected : d7781 p = 0) : d84099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7776 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7776, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4754 q selected
    | true =>
      simp only [d7776, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7777 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7777, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7777, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7778 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7778, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7778, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7779 q = 0) : d84097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7779, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7779, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7780 q = 0) : d84098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7780, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7780, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7781 q = 0) : d84099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7781, d84099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7781, d84099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4756 (p : Pattern) (selected : d7787 p = 0) : d84143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7784 q = 0) : d84140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d84140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7784, d84140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7785 q = 0) : d84141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d84141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7785, d84141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7786 q = 0) : d84142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d84142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7786, d84142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7787 q = 0) : d84143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7787, d84143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7787, d84143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4757 (p : Pattern) (selected : d7793 p = 0) : d84149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7755 q = 0) : d84120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4750 q selected
    | true =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d7756 q = 0) : d84121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7757 q = 0) : d84122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7758 q = 0) : d84123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7762 q = 0) : d84127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4751 q selected
    | true =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro404 q selected
  have h6 (q : Pattern) (selected : d7763 q = 0) : d84128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7764 q = 0) : d84129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7773 q = 0) : d84138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d84138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4753 q selected
    | true =>
      simp only [d7773, d84138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4746 q selected
  have h9 (q : Pattern) (selected : d7782 q = 0) : d84100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7782, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4755 q selected
    | true =>
      simp only [d7782, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h10 (q : Pattern) (selected : d7783 q = 0) : d84139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7783, d84139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7783, d84139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7788 q = 0) : d84144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4756 q selected
    | true =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7789 q = 0) : d84145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7790 q = 0) : d84146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7790, d84146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7790, d84146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7791 q = 0) : d84147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7791, d84147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7791, d84147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7792 q = 0) : d84148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7792, d84148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7792, d84148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7793 q = 0) : d84149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7793, d84149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7793, d84149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4758 (p : Pattern) (selected : d7794 p = 0) : d84150 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7732 q = 0) : d84097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7753 q = 0) : d84118 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7794 q = 0) : d84150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d84150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7794, d84150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4759 (p : Pattern) (selected : d7799 p = 0) : d84155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7731 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7759 q = 0) : d84124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7760 q = 0) : d84125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7799 q = 0) : d84155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d84155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7799, d84155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4760 (p : Pattern) (selected : d7803 p = 0) : d84159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7767 q = 0) : d84132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4752 q selected
    | true =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7768 q = 0) : d84133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7769 q = 0) : d84134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d84134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7769, d84134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7770 q = 0) : d84135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d84135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7770, d84135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7771 q = 0) : d84136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d84136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7771, d84136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7803 q = 0) : d84159 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, d84159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7803, d84159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4761 (p : Pattern) (selected : d7805 p = 0) : d84108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7776 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7776, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4754 q selected
    | true =>
      simp only [d7776, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7777 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7777, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7777, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7778 q = 0) : d84096 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7778, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7778, d84096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7779 q = 0) : d84097 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7779, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7779, d84097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7780 q = 0) : d84098 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7780, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7780, d84098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7805 q = 0) : d84108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7805, d84108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7805, d84108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4762 (p : Pattern) (selected : d7808 p = 0) : d84162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7729 q = 0) : d84094 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4745 q selected
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7730 q = 0) : d84095 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7784 q = 0) : d84140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d84140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7784, d84140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7785 q = 0) : d84141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, d84141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7785, d84141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7786 q = 0) : d84142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, d84142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7786, d84142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7808 q = 0) : d84162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7808, d84162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7808, d84162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4763 (p : Pattern) (selected : d7814 p = 0) : d84168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7755 q = 0) : d84120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4750 q selected
    | true =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d7756 q = 0) : d84121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7757 q = 0) : d84122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7758 q = 0) : d84123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7762 q = 0) : d84127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4751 q selected
    | true =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro404 q selected
  have h6 (q : Pattern) (selected : d7763 q = 0) : d84128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7764 q = 0) : d84129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7773 q = 0) : d84138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d84138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4753 q selected
    | true =>
      simp only [d7773, d84138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4746 q selected
  have h9 (q : Pattern) (selected : d7782 q = 0) : d84100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7782, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4755 q selected
    | true =>
      simp only [d7782, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h10 (q : Pattern) (selected : d7783 q = 0) : d84139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7783, d84139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7783, d84139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7788 q = 0) : d84144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4756 q selected
    | true =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7789 q = 0) : d84145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7790 q = 0) : d84146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7790, d84146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7790, d84146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7791 q = 0) : d84147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7791, d84147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7791, d84147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7792 q = 0) : d84148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7792, d84148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7792, d84148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7795 q = 0) : d84151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d84151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4758 q selected
    | true =>
      simp only [d7795, d84151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro428 q selected
  have h17 (q : Pattern) (selected : d7796 q = 0) : d84152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d84152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7796, d84152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7797 q = 0) : d84153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d84153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7797, d84153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7798 q = 0) : d84154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d84154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7798, d84154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7800 q = 0) : d84156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d84156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4759 q selected
    | true =>
      simp only [d7800, d84156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro430 q selected
  have h21 (q : Pattern) (selected : d7801 q = 0) : d84157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d84157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7801, d84157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7802 q = 0) : d84158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d84158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7802, d84158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7804 q = 0) : d84160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d84160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4760 q selected
    | true =>
      simp only [d7804, d84160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4748 q selected
  have h24 (q : Pattern) (selected : d7806 q = 0) : d84109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7806, d84109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4761 q selected
    | true =>
      simp only [d7806, d84109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro433 q selected
  have h25 (q : Pattern) (selected : d7807 q = 0) : d84161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7807, d84161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7807, d84161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7809 q = 0) : d84163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4762 q selected
    | true =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7810 q = 0) : d84164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7811 q = 0) : d84165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7811, d84165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7811, d84165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7812 q = 0) : d84166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7812, d84166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7812, d84166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7813 q = 0) : d84167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7813, d84167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7813, d84167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7814 q = 0) : d84168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7814, d84168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7814, d84168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4764 (p : Pattern) (selected : d7816 p = 0) : d84170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7735 q = 0) : d84100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4746 q selected
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d7736 q = 0) : d84101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7737 q = 0) : d84102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7738 q = 0) : d84103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7739 q = 0) : d84104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1350 q = 0) : d52838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1351 q = 0) : d52839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1352 q = 0) : d52840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1353 q = 0) : d52841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1354 q = 0) : d52842 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7816 q = 0) : d84170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d84170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7816, d84170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4765 (p : Pattern) (selected : d7823 p = 0) : d84177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7804 q = 0) : d84160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d84160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4760 q selected
    | true =>
      simp only [d7804, d84160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4748 q selected
  have h2 (q : Pattern) (selected : d7806 q = 0) : d84109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7806, d84109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4761 q selected
    | true =>
      simp only [d7806, d84109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro433 q selected
  have h3 (q : Pattern) (selected : d7807 q = 0) : d84161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7807, d84161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7807, d84161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7809 q = 0) : d84163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4762 q selected
    | true =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7810 q = 0) : d84164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7811 q = 0) : d84165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7811, d84165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7811, d84165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7821 q = 0) : d84175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7821, d84175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7821, d84175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7822 q = 0) : d84176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7822, d84176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7822, d84176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7823 q = 0) : d84177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7823, d84177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7823, d84177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4766 (p : Pattern) (selected : d7830 p = 0) : d84184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1397 q = 0) : d52885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro439 q selected
    | true =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
  have h2 (q : Pattern) (selected : d1398 q = 0) : d52886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1399 q = 0) : d52887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1402 q = 0) : d52890 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h5 (q : Pattern) (selected : d1403 q = 0) : d52891 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1404 q = 0) : d52892 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1405 q = 0) : d52893 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d52893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1405, d52893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7829 q = 0) : d84183 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7829, d84183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7829, d84183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7830 q = 0) : d84184 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7830, d84184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7830, d84184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4767 (p : Pattern) (selected : d7834 p = 0) : d84188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1402 q = 0) : d52890 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h2 (q : Pattern) (selected : d1403 q = 0) : d52891 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1404 q = 0) : d52892 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1412 q = 0) : d52900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h5 (q : Pattern) (selected : d1413 q = 0) : d52901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1414 q = 0) : d52902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1415 q = 0) : d52903 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d52903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1415, d52903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7833 q = 0) : d84187 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7833, d84187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7833, d84187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7834 q = 0) : d84188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7834, d84188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7834, d84188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4768 (p : Pattern) (selected : d7840 p = 0) : d84194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7831 q = 0) : d84185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7831, d84185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4766 q selected
    | true =>
      simp only [d7831, d84185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7832 q = 0) : d84186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7832, d84186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7832, d84186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7835 q = 0) : d84189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4767 q selected
    | true =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7836 q = 0) : d84190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7837 q = 0) : d84191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, d84191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7837, d84191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7838 q = 0) : d84192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, d84192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7838, d84192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7839 q = 0) : d84193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, d84193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7839, d84193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7840 q = 0) : d84194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, d84194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7840, d84194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4769 (p : Pattern) (selected : d7844 p = 0) : d84198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7835 q = 0) : d84189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4767 q selected
    | true =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7836 q = 0) : d84190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1431 q = 0) : d52919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro446 q selected
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1432 q = 0) : d52920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7841 q = 0) : d84195 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d84195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7841, d84195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7842 q = 0) : d84196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d84196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7842, d84196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7843 q = 0) : d84197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d84197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7843, d84197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7844 q = 0) : d84198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d84198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7844, d84198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4770 (p : Pattern) (selected : d7847 p = 0) : d84188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1455 q = 0) : d52890 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1455, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro448 q selected
    | true =>
      simp only [d1455, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro449 q selected
  have h2 (q : Pattern) (selected : d1456 q = 0) : d52891 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1456, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1456, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1457 q = 0) : d52892 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1457, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1457, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1464 q = 0) : d52900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1464, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro449 q selected
    | true =>
      simp only [d1464, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro450 q selected
  have h5 (q : Pattern) (selected : d1465 q = 0) : d52901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1465, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1465, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1466 q = 0) : d52902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1466, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1466, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1467 q = 0) : d52903 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1467, d52903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1467, d52903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7846 q = 0) : d84187 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7846, d84187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7846, d84187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7847 q = 0) : d84188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7847, d84188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7847, d84188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4771 (p : Pattern) (selected : d7853 p = 0) : d84198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7848 q = 0) : d84189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7848, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4770 q selected
    | true =>
      simp only [d7848, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7849 q = 0) : d84190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7849, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7849, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1475 q = 0) : d52919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1475, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro452 q selected
    | true =>
      simp only [d1475, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1476 q = 0) : d52920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1476, d52920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1476, d52920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7850 q = 0) : d84195 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7850, d84195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7850, d84195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7851 q = 0) : d84196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7851, d84196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7851, d84196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7852 q = 0) : d84197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7852, d84197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7852, d84197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7853 q = 0) : d84198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7853, d84198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7853, d84198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4772 (p : Pattern) (selected : d7859 p = 0) : d84205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7835 q = 0) : d84189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4767 q selected
    | true =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7836 q = 0) : d84190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7856 q = 0) : d84202 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7856, d84202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7856, d84202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7857 q = 0) : d84203 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7857, d84203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7857, d84203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7858 q = 0) : d84204 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7858, d84204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7858, d84204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7859 q = 0) : d84205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7859, d84205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7859, d84205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4773 (p : Pattern) (selected : d7865 p = 0) : d84211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7845 q = 0) : d84199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, d84199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4768 q selected
    | true =>
      simp only [d7845, d84199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4769 q selected
  have h2 (q : Pattern) (selected : d7854 q = 0) : d84200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7854, d84200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4771 q selected
    | true =>
      simp only [d7854, d84200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro454 q selected
  have h3 (q : Pattern) (selected : d7855 q = 0) : d84201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7855, d84201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7855, d84201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7860 q = 0) : d84206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, d84206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4772 q selected
    | true =>
      simp only [d7860, d84206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7861 q = 0) : d84207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, d84207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7861, d84207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7862 q = 0) : d84208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7862, d84208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7862, d84208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7863 q = 0) : d84209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7863, d84209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7863, d84209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7864 q = 0) : d84210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7864, d84210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7864, d84210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7865 q = 0) : d84211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7865, d84211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7865, d84211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4774 (p : Pattern) (selected : d7871 p = 0) : d84217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7741 q = 0) : d84106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d84106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7741, d84106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4747 q selected
  have h2 (q : Pattern) (selected : d7742 q = 0) : d84107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d84107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7742, d84107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7750 q = 0) : d84115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d84115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4747 q selected
    | true =>
      simp only [d7750, d84115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4749 q selected
  have h4 (q : Pattern) (selected : d7751 q = 0) : d84116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d84116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7751, d84116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7752 q = 0) : d84117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d84117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7752, d84117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7815 q = 0) : d84169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7815, d84169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4757 q selected
    | true =>
      simp only [d7815, d84169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4763 q selected
  have h7 (q : Pattern) (selected : d7817 q = 0) : d84171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d84171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4764 q selected
    | true =>
      simp only [d7817, d84171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro436 q selected
  have h8 (q : Pattern) (selected : d7818 q = 0) : d84172 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7818, d84172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7818, d84172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7819 q = 0) : d84173 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7819, d84173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7819, d84173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7820 q = 0) : d84174 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7820, d84174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7820, d84174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7824 q = 0) : d84178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7824, d84178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7824, d84178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4765 q selected
  have h12 (q : Pattern) (selected : d1371 q = 0) : d52859 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro438 q selected
  have h13 (q : Pattern) (selected : d7825 q = 0) : d84179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7825, d84179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7825, d84179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7826 q = 0) : d84180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7826, d84180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7826, d84180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7827 q = 0) : d84181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7827, d84181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7827, d84181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7828 q = 0) : d84182 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7828, d84182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7828, d84182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7866 q = 0) : d84212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7866, d84212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7866, d84212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4773 q selected
  have h18 (q : Pattern) (selected : d1504 q = 0) : d52945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro457 q selected
  have h19 (q : Pattern) (selected : d7867 q = 0) : d84213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7867, d84213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7867, d84213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7868 q = 0) : d84214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7868, d84214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7868, d84214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d7869 q = 0) : d84215 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7869, d84215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d7869, d84215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d7870 q = 0) : d84216 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7870, d84216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7870, d84216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7871 q = 0) : d84217 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7871, d84217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7871, d84217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4775 (p : Pattern) (selected : d7877 p = 0) : d84223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7872 q = 0) : d84218 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7872, d84218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7872, d84218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4774 q selected
  have h2 (q : Pattern) (selected : d7873 q = 0) : d84219 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7873, d84219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7873, d84219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7874 q = 0) : d84220 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7874, d84220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7874, d84220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7875 q = 0) : d84221 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7875, d84221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7875, d84221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7876 q = 0) : d84222 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7876, d84222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7876, d84222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7877 q = 0) : d84223 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7877, d84223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7877, d84223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4776 (p : Pattern) (selected : d7882 p = 0) : d84228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1590 q = 0) : d53031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h2 (q : Pattern) (selected : d1591 q = 0) : d53032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1592 q = 0) : d53033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1603 q = 0) : d53044 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
    | true =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h5 (q : Pattern) (selected : d1604 q = 0) : d53045 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1605 q = 0) : d53046 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1606 q = 0) : d53047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d53047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1606, d53047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7881 q = 0) : d84227 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7881, d84227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7881, d84227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7882 q = 0) : d84228 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7882, d84228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7882, d84228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4777 (p : Pattern) (selected : d7888 p = 0) : d84234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 0) : d84232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7887 q = 0) : d84233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7888 q = 0) : d84234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d84234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7888, d84234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4778 (p : Pattern) (selected : d7894 p = 0) : d84240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7889 q = 0) : d84235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4777 q selected
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d7890 q = 0) : d84236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7891 q = 0) : d84237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7892 q = 0) : d84238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7893 q = 0) : d84239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7894 q = 0) : d84240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d84240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7894, d84240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4779 (p : Pattern) (selected : d7897 p = 0) : d84243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 0) : d84232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7887 q = 0) : d84233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7897 q = 0) : d84243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d84243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7897, d84243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4780 (p : Pattern) (selected : d7903 p = 0) : d84249 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7889 q = 0) : d84235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4777 q selected
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d7890 q = 0) : d84236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7891 q = 0) : d84237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7892 q = 0) : d84238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7893 q = 0) : d84239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7898 q = 0) : d84244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4779 q selected
    | true =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro481 q selected
  have h7 (q : Pattern) (selected : d7899 q = 0) : d84245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d84245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7899, d84245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7900 q = 0) : d84246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d84246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7900, d84246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7901 q = 0) : d84247 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d84247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7901, d84247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7902 q = 0) : d84248 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d84248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7902, d84248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7903 q = 0) : d84249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d84249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7903, d84249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4781 (p : Pattern) (selected : d7908 p = 0) : d84254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 0) : d84232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7907 q = 0) : d84253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7908 q = 0) : d84254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d84254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7908, d84254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4782 (p : Pattern) (selected : d7915 p = 0) : d84261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7913 q = 0) : d84259 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7914 q = 0) : d84260 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7915 q = 0) : d84261 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d84261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7915, d84261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4783 (p : Pattern) (selected : d7920 p = 0) : d84266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1671 q = 0) : d53112 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro488 q selected
    | true =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
  have h2 (q : Pattern) (selected : d1672 q = 0) : d53113 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1673 q = 0) : d53114 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1590 q = 0) : d53031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h5 (q : Pattern) (selected : d1591 q = 0) : d53032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1592 q = 0) : d53033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1674 q = 0) : d53115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d53115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1674, d53115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7919 q = 0) : d84265 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7919, d84265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7919, d84265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7920 q = 0) : d84266 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7920, d84266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7920, d84266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4784 (p : Pattern) (selected : d7926 p = 0) : d84272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7921 q = 0) : d84267 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4783 q selected
    | true =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7922 q = 0) : d84268 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7923 q = 0) : d84269 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d84269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7923, d84269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7924 q = 0) : d84270 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d84270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7924, d84270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7925 q = 0) : d84271 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d84271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7925, d84271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7926 q = 0) : d84272 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, d84272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7926, d84272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4785 (p : Pattern) (selected : d7929 p = 0) : d84228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1761 q = 0) : d53031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1761, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro504 q selected
    | true =>
      simp only [d1761, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro505 q selected
  have h2 (q : Pattern) (selected : d1762 q = 0) : d53032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1762, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1762, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1763 q = 0) : d53033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1763, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1763, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1774 q = 0) : d53044 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1774, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro505 q selected
    | true =>
      simp only [d1774, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro507 q selected
  have h5 (q : Pattern) (selected : d1775 q = 0) : d53045 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1775, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1775, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1776 q = 0) : d53046 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1776, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1776, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1777 q = 0) : d53047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1777, d53047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1777, d53047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7928 q = 0) : d84227 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7928, d84227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7928, d84227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7929 q = 0) : d84228 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7929, d84228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7929, d84228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4786 (p : Pattern) (selected : d7935 p = 0) : d84234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7930 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7930, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4785 q selected
    | true =>
      simp only [d7930, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7931 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7931, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7931, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7932 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7932, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7932, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7933 q = 0) : d84232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7933, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7933, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7934 q = 0) : d84233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7934, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7934, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7935 q = 0) : d84234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7935, d84234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7935, d84234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4787 (p : Pattern) (selected : d7941 p = 0) : d84278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7938 q = 0) : d84275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d84275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7938, d84275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7939 q = 0) : d84276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d84276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7939, d84276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7940 q = 0) : d84277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d84277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7940, d84277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7941 q = 0) : d84278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7941, d84278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7941, d84278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4788 (p : Pattern) (selected : d7947 p = 0) : d84284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7909 q = 0) : d84255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4781 q selected
    | true =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d7910 q = 0) : d84256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7911 q = 0) : d84257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7912 q = 0) : d84258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7916 q = 0) : d84262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4782 q selected
    | true =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro486 q selected
  have h6 (q : Pattern) (selected : d7917 q = 0) : d84263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7918 q = 0) : d84264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7927 q = 0) : d84273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d84273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4784 q selected
    | true =>
      simp only [d7927, d84273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4777 q selected
  have h9 (q : Pattern) (selected : d7936 q = 0) : d84235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7936, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4786 q selected
    | true =>
      simp only [d7936, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h10 (q : Pattern) (selected : d7937 q = 0) : d84274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7937, d84274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7937, d84274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7942 q = 0) : d84279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4787 q selected
    | true =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7943 q = 0) : d84280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7944 q = 0) : d84281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7944, d84281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7944, d84281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7945 q = 0) : d84282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7945, d84282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7945, d84282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7946 q = 0) : d84283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7946, d84283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7946, d84283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7947 q = 0) : d84284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7947, d84284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7947, d84284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4789 (p : Pattern) (selected : d7948 p = 0) : d84285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7886 q = 0) : d84232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7907 q = 0) : d84253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7948 q = 0) : d84285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d84285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7948, d84285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4790 (p : Pattern) (selected : d7953 p = 0) : d84290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7885 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7913 q = 0) : d84259 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7914 q = 0) : d84260 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7953 q = 0) : d84290 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d84290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7953, d84290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4791 (p : Pattern) (selected : d7957 p = 0) : d84294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7921 q = 0) : d84267 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4783 q selected
    | true =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7922 q = 0) : d84268 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7923 q = 0) : d84269 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d84269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7923, d84269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7924 q = 0) : d84270 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d84270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7924, d84270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7925 q = 0) : d84271 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d84271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7925, d84271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7957 q = 0) : d84294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, d84294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7957, d84294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4792 (p : Pattern) (selected : d7959 p = 0) : d84243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7930 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7930, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4785 q selected
    | true =>
      simp only [d7930, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7931 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7931, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7931, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7932 q = 0) : d84231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7932, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7932, d84231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7933 q = 0) : d84232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7933, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7933, d84232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7934 q = 0) : d84233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7934, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7934, d84233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7959 q = 0) : d84243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7959, d84243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7959, d84243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4793 (p : Pattern) (selected : d7962 p = 0) : d84297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7883 q = 0) : d84229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4776 q selected
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7884 q = 0) : d84230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7938 q = 0) : d84275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d84275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7938, d84275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7939 q = 0) : d84276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, d84276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7939, d84276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7940 q = 0) : d84277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, d84277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7940, d84277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7962 q = 0) : d84297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7962, d84297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7962, d84297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4794 (p : Pattern) (selected : d7968 p = 0) : d84303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7909 q = 0) : d84255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4781 q selected
    | true =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d7910 q = 0) : d84256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7911 q = 0) : d84257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7912 q = 0) : d84258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7916 q = 0) : d84262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4782 q selected
    | true =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro486 q selected
  have h6 (q : Pattern) (selected : d7917 q = 0) : d84263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7918 q = 0) : d84264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7927 q = 0) : d84273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d84273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4784 q selected
    | true =>
      simp only [d7927, d84273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4777 q selected
  have h9 (q : Pattern) (selected : d7936 q = 0) : d84235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7936, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4786 q selected
    | true =>
      simp only [d7936, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h10 (q : Pattern) (selected : d7937 q = 0) : d84274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7937, d84274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7937, d84274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7942 q = 0) : d84279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4787 q selected
    | true =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d7943 q = 0) : d84280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d7944 q = 0) : d84281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7944, d84281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7944, d84281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7945 q = 0) : d84282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7945, d84282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7945, d84282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d7946 q = 0) : d84283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7946, d84283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7946, d84283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7949 q = 0) : d84286 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d84286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4789 q selected
    | true =>
      simp only [d7949, d84286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro514 q selected
  have h17 (q : Pattern) (selected : d7950 q = 0) : d84287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d84287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7950, d84287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7951 q = 0) : d84288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d84288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7951, d84288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d7952 q = 0) : d84289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d84289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7952, d84289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d7954 q = 0) : d84291 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d84291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4790 q selected
    | true =>
      simp only [d7954, d84291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro516 q selected
  have h21 (q : Pattern) (selected : d7955 q = 0) : d84292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d84292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7955, d84292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d7956 q = 0) : d84293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d84293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d7956, d84293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d7958 q = 0) : d84295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d84295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4791 q selected
    | true =>
      simp only [d7958, d84295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4779 q selected
  have h24 (q : Pattern) (selected : d7960 q = 0) : d84244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7960, d84244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4792 q selected
    | true =>
      simp only [d7960, d84244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro519 q selected
  have h25 (q : Pattern) (selected : d7961 q = 0) : d84296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7961, d84296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d7961, d84296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d7963 q = 0) : d84298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4793 q selected
    | true =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d7964 q = 0) : d84299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d7965 q = 0) : d84300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7965, d84300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d7965, d84300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d7966 q = 0) : d84301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7966, d84301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d7966, d84301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d7967 q = 0) : d84302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7967, d84302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d7967, d84302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d7968 q = 0) : d84303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7968, d84303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7968, d84303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4795 (p : Pattern) (selected : d7970 p = 0) : d84305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7889 q = 0) : d84235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4777 q selected
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d7890 q = 0) : d84236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7891 q = 0) : d84237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7892 q = 0) : d84238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7893 q = 0) : d84239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1827 q = 0) : d53153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1828 q = 0) : d53154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1829 q = 0) : d53155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1830 q = 0) : d53156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1831 q = 0) : d53157 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7970 q = 0) : d84305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d84305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7970, d84305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4796 (p : Pattern) (selected : d7977 p = 0) : d84312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7958 q = 0) : d84295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d84295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4791 q selected
    | true =>
      simp only [d7958, d84295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4779 q selected
  have h2 (q : Pattern) (selected : d7960 q = 0) : d84244 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7960, d84244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4792 q selected
    | true =>
      simp only [d7960, d84244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro519 q selected
  have h3 (q : Pattern) (selected : d7961 q = 0) : d84296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7961, d84296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7961, d84296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7963 q = 0) : d84298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4793 q selected
    | true =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7964 q = 0) : d84299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d7965 q = 0) : d84300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7965, d84300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7965, d84300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7975 q = 0) : d84310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7975, d84310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7975, d84310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7976 q = 0) : d84311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7976, d84311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7976, d84311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7977 q = 0) : d84312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7977, d84312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7977, d84312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4797 (p : Pattern) (selected : d7984 p = 0) : d84319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1874 q = 0) : d53200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro525 q selected
    | true =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
  have h2 (q : Pattern) (selected : d1875 q = 0) : d53201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1876 q = 0) : d53202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1879 q = 0) : d53205 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h5 (q : Pattern) (selected : d1880 q = 0) : d53206 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1881 q = 0) : d53207 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1882 q = 0) : d53208 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d53208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1882, d53208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7983 q = 0) : d84318 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7983, d84318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7983, d84318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7984 q = 0) : d84319 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7984, d84319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7984, d84319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4798 (p : Pattern) (selected : d7988 p = 0) : d84323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1879 q = 0) : d53205 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h2 (q : Pattern) (selected : d1880 q = 0) : d53206 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1881 q = 0) : d53207 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1889 q = 0) : d53215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h5 (q : Pattern) (selected : d1890 q = 0) : d53216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1891 q = 0) : d53217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1892 q = 0) : d53218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d53218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1892, d53218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7987 q = 0) : d84322 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7987, d84322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7987, d84322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7988 q = 0) : d84323 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7988, d84323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7988, d84323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4799 (p : Pattern) (selected : d7994 p = 0) : d84329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7985 q = 0) : d84320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7985, d84320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4797 q selected
    | true =>
      simp only [d7985, d84320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7986 q = 0) : d84321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7986, d84321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7986, d84321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7989 q = 0) : d84324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4798 q selected
    | true =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d7990 q = 0) : d84325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7991 q = 0) : d84326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, d84326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7991, d84326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7992 q = 0) : d84327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, d84327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7992, d84327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7993 q = 0) : d84328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, d84328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7993, d84328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7994 q = 0) : d84329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, d84329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7994, d84329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4800 (p : Pattern) (selected : d7998 p = 0) : d84333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7989 q = 0) : d84324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4798 q selected
    | true =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7990 q = 0) : d84325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1908 q = 0) : d53234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro532 q selected
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1909 q = 0) : d53235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7995 q = 0) : d84330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d84330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7995, d84330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7996 q = 0) : d84331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d84331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7996, d84331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7997 q = 0) : d84332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d84332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7997, d84332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7998 q = 0) : d84333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d84333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7998, d84333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4801 (p : Pattern) (selected : d8001 p = 0) : d84323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1932 q = 0) : d53205 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1932, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro534 q selected
    | true =>
      simp only [d1932, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro535 q selected
  have h2 (q : Pattern) (selected : d1933 q = 0) : d53206 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1933, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1933, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1934 q = 0) : d53207 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1934, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1934, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1941 q = 0) : d53215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1941, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro535 q selected
    | true =>
      simp only [d1941, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro536 q selected
  have h5 (q : Pattern) (selected : d1942 q = 0) : d53216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1942, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1942, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1943 q = 0) : d53217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1943, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1943, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1944 q = 0) : d53218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1944, d53218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1944, d53218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8000 q = 0) : d84322 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8000, d84322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8000, d84322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8001 q = 0) : d84323 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8001, d84323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8001, d84323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4802 (p : Pattern) (selected : d8007 p = 0) : d84333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8002 q = 0) : d84324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8002, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4801 q selected
    | true =>
      simp only [d8002, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8003 q = 0) : d84325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8003, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8003, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1952 q = 0) : d53234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1952, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro538 q selected
    | true =>
      simp only [d1952, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1953 q = 0) : d53235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1953, d53235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1953, d53235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8004 q = 0) : d84330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8004, d84330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8004, d84330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8005 q = 0) : d84331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8005, d84331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8005, d84331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8006 q = 0) : d84332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8006, d84332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8006, d84332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8007 q = 0) : d84333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8007, d84333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8007, d84333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4803 (p : Pattern) (selected : d8013 p = 0) : d84340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7989 q = 0) : d84324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4798 q selected
    | true =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7990 q = 0) : d84325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8010 q = 0) : d84337 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8010, d84337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8010, d84337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8011 q = 0) : d84338 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8011, d84338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8011, d84338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8012 q = 0) : d84339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8012, d84339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8012, d84339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8013 q = 0) : d84340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8013, d84340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8013, d84340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4804 (p : Pattern) (selected : d8019 p = 0) : d84346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7999 q = 0) : d84334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, d84334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4799 q selected
    | true =>
      simp only [d7999, d84334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4800 q selected
  have h2 (q : Pattern) (selected : d8008 q = 0) : d84335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8008, d84335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4802 q selected
    | true =>
      simp only [d8008, d84335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro540 q selected
  have h3 (q : Pattern) (selected : d8009 q = 0) : d84336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8009, d84336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8009, d84336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8014 q = 0) : d84341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, d84341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4803 q selected
    | true =>
      simp only [d8014, d84341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8015 q = 0) : d84342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, d84342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8015, d84342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8016 q = 0) : d84343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8016, d84343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8016, d84343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8017 q = 0) : d84344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8017, d84344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8017, d84344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8018 q = 0) : d84345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8018, d84345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8018, d84345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8019 q = 0) : d84346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8019, d84346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8019, d84346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4805 (p : Pattern) (selected : d8025 p = 0) : d84352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d7895 q = 0) : d84241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d84241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7895, d84241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4778 q selected
  have h2 (q : Pattern) (selected : d7896 q = 0) : d84242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d84242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7896, d84242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7904 q = 0) : d84250 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d84250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4778 q selected
    | true =>
      simp only [d7904, d84250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4780 q selected
  have h4 (q : Pattern) (selected : d7905 q = 0) : d84251 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d84251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7905, d84251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7906 q = 0) : d84252 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d84252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7906, d84252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7969 q = 0) : d84304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7969, d84304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4788 q selected
    | true =>
      simp only [d7969, d84304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4794 q selected
  have h7 (q : Pattern) (selected : d7971 q = 0) : d84306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d84306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4795 q selected
    | true =>
      simp only [d7971, d84306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro522 q selected
  have h8 (q : Pattern) (selected : d7972 q = 0) : d84307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7972, d84307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7972, d84307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7973 q = 0) : d84308 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7973, d84308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7973, d84308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d7974 q = 0) : d84309 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7974, d84309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7974, d84309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7978 q = 0) : d84313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7978, d84313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7978, d84313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4796 q selected
  have h12 (q : Pattern) (selected : d1848 q = 0) : d53174 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro524 q selected
  have h13 (q : Pattern) (selected : d7979 q = 0) : d84314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7979, d84314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7979, d84314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7980 q = 0) : d84315 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7980, d84315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7980, d84315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d7981 q = 0) : d84316 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7981, d84316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7981, d84316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d7982 q = 0) : d84317 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7982, d84317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7982, d84317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d8020 q = 0) : d84347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8020, d84347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8020, d84347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4804 q selected
  have h18 (q : Pattern) (selected : d1981 q = 0) : d53260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro543 q selected
  have h19 (q : Pattern) (selected : d8021 q = 0) : d84348 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8021, d84348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8021, d84348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d8022 q = 0) : d84349 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8022, d84349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d8022, d84349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d8023 q = 0) : d84350 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8023, d84350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d8023, d84350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d8024 q = 0) : d84351 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8024, d84351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d8024, d84351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d8025 q = 0) : d84352 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d8025, d84352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d8025, d84352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4806 (p : Pattern) (selected : d8031 p = 0) : d84358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8026 q = 0) : d84353 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d8026, d84353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8026, d84353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4805 q selected
  have h2 (q : Pattern) (selected : d8027 q = 0) : d84354 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d8027, d84354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8027, d84354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8028 q = 0) : d84355 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d8028, d84355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8028, d84355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8029 q = 0) : d84356 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d8029, d84356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8029, d84356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8030 q = 0) : d84357 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d8030, d84357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8030, d84357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8031 q = 0) : d84358 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d8031, d84358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8031, d84358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4807 (p : Pattern) (selected : d8037 p = 0) : d84364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2073 q = 0) : d53352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h2 (q : Pattern) (selected : d2074 q = 0) : d53353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2075 q = 0) : d53354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2086 q = 0) : d53365 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
    | true =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h5 (q : Pattern) (selected : d2087 q = 0) : d53366 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2088 q = 0) : d53367 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2089 q = 0) : d53368 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d53368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2089, d53368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8036 q = 0) : d84363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8036, d84363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8036, d84363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8037 q = 0) : d84364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8037, d84364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8037, d84364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4808 (p : Pattern) (selected : d8043 p = 0) : d84370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 0) : d84368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8042 q = 0) : d84369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8043 q = 0) : d84370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d84370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8043, d84370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4809 (p : Pattern) (selected : d8049 p = 0) : d84376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8044 q = 0) : d84371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4808 q selected
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d8045 q = 0) : d84372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8046 q = 0) : d84373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8047 q = 0) : d84374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8048 q = 0) : d84375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8049 q = 0) : d84376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d84376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8049, d84376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4810 (p : Pattern) (selected : d8052 p = 0) : d84379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 0) : d84368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8042 q = 0) : d84369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8052 q = 0) : d84379 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d84379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8052, d84379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4811 (p : Pattern) (selected : d8058 p = 0) : d84385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8044 q = 0) : d84371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4808 q selected
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d8045 q = 0) : d84372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8046 q = 0) : d84373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8047 q = 0) : d84374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8048 q = 0) : d84375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8053 q = 0) : d84380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4810 q selected
    | true =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro570 q selected
  have h7 (q : Pattern) (selected : d8054 q = 0) : d84381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d84381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8054, d84381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8055 q = 0) : d84382 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d84382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8055, d84382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8056 q = 0) : d84383 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d84383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8056, d84383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8057 q = 0) : d84384 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d84384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8057, d84384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8058 q = 0) : d84385 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d84385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8058, d84385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4812 (p : Pattern) (selected : d8063 p = 0) : d84390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 0) : d84368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8062 q = 0) : d84389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8063 q = 0) : d84390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d84390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8063, d84390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4813 (p : Pattern) (selected : d8070 p = 0) : d84397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8068 q = 0) : d84395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8069 q = 0) : d84396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8070 q = 0) : d84397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d84397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8070, d84397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4814 (p : Pattern) (selected : d8075 p = 0) : d84402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2150 q = 0) : d53429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro577 q selected
    | true =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
  have h2 (q : Pattern) (selected : d2151 q = 0) : d53430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2152 q = 0) : d53431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2073 q = 0) : d53352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h5 (q : Pattern) (selected : d2074 q = 0) : d53353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2075 q = 0) : d53354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2153 q = 0) : d53432 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d53432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2153, d53432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8074 q = 0) : d84401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8074, d84401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8074, d84401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8075 q = 0) : d84402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8075, d84402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8075, d84402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4815 (p : Pattern) (selected : d8081 p = 0) : d84408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8076 q = 0) : d84403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4814 q selected
    | true =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8077 q = 0) : d84404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8078 q = 0) : d84405 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d84405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8078, d84405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8079 q = 0) : d84406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d84406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8079, d84406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8080 q = 0) : d84407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d84407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8080, d84407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8081 q = 0) : d84408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, d84408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8081, d84408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4816 (p : Pattern) (selected : d8084 p = 0) : d84364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2239 q = 0) : d53352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2239, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro594 q selected
    | true =>
      simp only [d2239, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro595 q selected
  have h2 (q : Pattern) (selected : d2240 q = 0) : d53353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2240, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2240, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2241 q = 0) : d53354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2241, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2241, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2252 q = 0) : d53365 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2252, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro595 q selected
    | true =>
      simp only [d2252, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro597 q selected
  have h5 (q : Pattern) (selected : d2253 q = 0) : d53366 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2253, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2253, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2254 q = 0) : d53367 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2254, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2254, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2255 q = 0) : d53368 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2255, d53368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2255, d53368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8083 q = 0) : d84363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8083, d84363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8083, d84363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8084 q = 0) : d84364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8084, d84364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8084, d84364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4817 (p : Pattern) (selected : d8090 p = 0) : d84370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8085 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8085, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4816 q selected
    | true =>
      simp only [d8085, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8086 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8086, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8086, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro599 q selected
    | true =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8087 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8087, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8087, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8088 q = 0) : d84368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8088, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8088, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8089 q = 0) : d84369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8089, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8089, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8090 q = 0) : d84370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8090, d84370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8090, d84370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4818 (p : Pattern) (selected : d8096 p = 0) : d84414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8093 q = 0) : d84411 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d84411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8093, d84411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8094 q = 0) : d84412 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d84412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8094, d84412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8095 q = 0) : d84413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d84413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8095, d84413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8096 q = 0) : d84414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8096, d84414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8096, d84414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4819 (p : Pattern) (selected : d8102 p = 0) : d84420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8064 q = 0) : d84391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4812 q selected
    | true =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d8065 q = 0) : d84392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8066 q = 0) : d84393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8067 q = 0) : d84394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8071 q = 0) : d84398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4813 q selected
    | true =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro575 q selected
  have h6 (q : Pattern) (selected : d8072 q = 0) : d84399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8073 q = 0) : d84400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8082 q = 0) : d84409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d84409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4815 q selected
    | true =>
      simp only [d8082, d84409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4808 q selected
  have h9 (q : Pattern) (selected : d8091 q = 0) : d84371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8091, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4817 q selected
    | true =>
      simp only [d8091, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h10 (q : Pattern) (selected : d8092 q = 0) : d84410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8092, d84410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8092, d84410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8097 q = 0) : d84415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4818 q selected
    | true =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d8098 q = 0) : d84416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d8099 q = 0) : d84417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8099, d84417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8099, d84417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8100 q = 0) : d84418 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8100, d84418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8100, d84418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8101 q = 0) : d84419 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8101, d84419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8101, d84419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8102 q = 0) : d84420 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8102, d84420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8102, d84420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4820 (p : Pattern) (selected : d8103 p = 0) : d84421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8041 q = 0) : d84368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8062 q = 0) : d84389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8103 q = 0) : d84421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d84421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8103, d84421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4821 (p : Pattern) (selected : d8108 p = 0) : d84426 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8040 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8068 q = 0) : d84395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8069 q = 0) : d84396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8108 q = 0) : d84426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d84426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8108, d84426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4822 (p : Pattern) (selected : d8112 p = 0) : d84430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8076 q = 0) : d84403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4814 q selected
    | true =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8077 q = 0) : d84404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8078 q = 0) : d84405 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d84405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8078, d84405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8079 q = 0) : d84406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d84406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8079, d84406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8080 q = 0) : d84407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d84407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8080, d84407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8112 q = 0) : d84430 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, d84430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8112, d84430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4823 (p : Pattern) (selected : d8114 p = 0) : d84379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8085 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8085, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4816 q selected
    | true =>
      simp only [d8085, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8086 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8086, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8086, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro599 q selected
    | true =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8087 q = 0) : d84367 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8087, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8087, d84367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8088 q = 0) : d84368 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8088, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8088, d84368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8089 q = 0) : d84369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8089, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8089, d84369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8114 q = 0) : d84379 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8114, d84379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8114, d84379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4824 (p : Pattern) (selected : d8117 p = 0) : d84433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8038 q = 0) : d84365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4807 q selected
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8039 q = 0) : d84366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8093 q = 0) : d84411 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d84411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8093, d84411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8094 q = 0) : d84412 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, d84412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8094, d84412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8095 q = 0) : d84413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, d84413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8095, d84413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8117 q = 0) : d84433 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8117, d84433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8117, d84433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4825 (p : Pattern) (selected : d8123 p = 0) : d84439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8064 q = 0) : d84391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4812 q selected
    | true =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d8065 q = 0) : d84392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8066 q = 0) : d84393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8067 q = 0) : d84394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8071 q = 0) : d84398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4813 q selected
    | true =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro575 q selected
  have h6 (q : Pattern) (selected : d8072 q = 0) : d84399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8073 q = 0) : d84400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8082 q = 0) : d84409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d84409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4815 q selected
    | true =>
      simp only [d8082, d84409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4808 q selected
  have h9 (q : Pattern) (selected : d8091 q = 0) : d84371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8091, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4817 q selected
    | true =>
      simp only [d8091, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h10 (q : Pattern) (selected : d8092 q = 0) : d84410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8092, d84410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8092, d84410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8097 q = 0) : d84415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4818 q selected
    | true =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d8098 q = 0) : d84416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d8099 q = 0) : d84417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8099, d84417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8099, d84417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8100 q = 0) : d84418 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8100, d84418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8100, d84418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8101 q = 0) : d84419 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8101, d84419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8101, d84419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8104 q = 0) : d84422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d84422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4820 q selected
    | true =>
      simp only [d8104, d84422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro604 q selected
  have h17 (q : Pattern) (selected : d8105 q = 0) : d84423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d84423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8105, d84423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d8106 q = 0) : d84424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d84424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8106, d84424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d8107 q = 0) : d84425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d84425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8107, d84425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d8109 q = 0) : d84427 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d84427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4821 q selected
    | true =>
      simp only [d8109, d84427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro606 q selected
  have h21 (q : Pattern) (selected : d8110 q = 0) : d84428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d84428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8110, d84428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d8111 q = 0) : d84429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d84429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d8111, d84429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d8113 q = 0) : d84431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d84431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4822 q selected
    | true =>
      simp only [d8113, d84431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4810 q selected
  have h24 (q : Pattern) (selected : d8115 q = 0) : d84380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8115, d84380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4823 q selected
    | true =>
      simp only [d8115, d84380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro609 q selected
  have h25 (q : Pattern) (selected : d8116 q = 0) : d84432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8116, d84432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d8116, d84432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d8118 q = 0) : d84434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4824 q selected
    | true =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d8119 q = 0) : d84435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d8120 q = 0) : d84436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8120, d84436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d8120, d84436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d8121 q = 0) : d84437 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8121, d84437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d8121, d84437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d8122 q = 0) : d84438 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8122, d84438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d8122, d84438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d8123 q = 0) : d84439 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8123, d84439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d8123, d84439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4826 (p : Pattern) (selected : d8125 p = 0) : d84441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8044 q = 0) : d84371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4808 q selected
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d8045 q = 0) : d84372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8046 q = 0) : d84373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8047 q = 0) : d84374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8048 q = 0) : d84375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2305 q = 0) : d53470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2306 q = 0) : d53471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2307 q = 0) : d53472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2308 q = 0) : d53473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2309 q = 0) : d53474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8125 q = 0) : d84441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d84441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8125, d84441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4827 (p : Pattern) (selected : d8132 p = 0) : d84448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8113 q = 0) : d84431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d84431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4822 q selected
    | true =>
      simp only [d8113, d84431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4810 q selected
  have h2 (q : Pattern) (selected : d8115 q = 0) : d84380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8115, d84380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4823 q selected
    | true =>
      simp only [d8115, d84380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro609 q selected
  have h3 (q : Pattern) (selected : d8116 q = 0) : d84432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8116, d84432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8116, d84432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8118 q = 0) : d84434 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4824 q selected
    | true =>
      simp only [d8118, d84434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8119 q = 0) : d84435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8119, d84435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8120 q = 0) : d84436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8120, d84436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8120, d84436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8130 q = 0) : d84446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8130, d84446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8130, d84446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8131 q = 0) : d84447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8131, d84447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8131, d84447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8132 q = 0) : d84448 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8132, d84448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8132, d84448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4828 (p : Pattern) (selected : d8139 p = 0) : d84455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2352 q = 0) : d53517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro615 q selected
    | true =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
  have h2 (q : Pattern) (selected : d2353 q = 0) : d53518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2354 q = 0) : d53519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2357 q = 0) : d53522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h5 (q : Pattern) (selected : d2358 q = 0) : d53523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2359 q = 0) : d53524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2360 q = 0) : d53525 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d53525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2360, d53525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8138 q = 0) : d84454 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8138, d84454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8138, d84454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8139 q = 0) : d84455 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8139, d84455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8139, d84455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4829 (p : Pattern) (selected : d8143 p = 0) : d84459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2357 q = 0) : d53522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h2 (q : Pattern) (selected : d2358 q = 0) : d53523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2359 q = 0) : d53524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2367 q = 0) : d53532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h5 (q : Pattern) (selected : d2368 q = 0) : d53533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2369 q = 0) : d53534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2370 q = 0) : d53535 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d53535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2370, d53535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8142 q = 0) : d84458 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8142, d84458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8142, d84458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8143 q = 0) : d84459 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8143, d84459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8143, d84459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4830 (p : Pattern) (selected : d8149 p = 0) : d84465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8140 q = 0) : d84456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8140, d84456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4828 q selected
    | true =>
      simp only [d8140, d84456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8141 q = 0) : d84457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8141, d84457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8141, d84457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8144 q = 0) : d84460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4829 q selected
    | true =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8145 q = 0) : d84461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8146 q = 0) : d84462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, d84462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8146, d84462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8147 q = 0) : d84463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, d84463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8147, d84463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8148 q = 0) : d84464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, d84464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8148, d84464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8149 q = 0) : d84465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, d84465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8149, d84465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4831 (p : Pattern) (selected : d8153 p = 0) : d84469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8144 q = 0) : d84460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4829 q selected
    | true =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8145 q = 0) : d84461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2386 q = 0) : d53551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro622 q selected
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2387 q = 0) : d53552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8150 q = 0) : d84466 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d84466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8150, d84466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8151 q = 0) : d84467 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d84467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8151, d84467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8152 q = 0) : d84468 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d84468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8152, d84468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8153 q = 0) : d84469 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d84469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8153, d84469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4832 (p : Pattern) (selected : d8156 p = 0) : d84459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2410 q = 0) : d53522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2410, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro624 q selected
    | true =>
      simp only [d2410, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro625 q selected
  have h2 (q : Pattern) (selected : d2411 q = 0) : d53523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2411, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2411, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2412 q = 0) : d53524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2412, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2412, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2419 q = 0) : d53532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2419, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro625 q selected
    | true =>
      simp only [d2419, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro626 q selected
  have h5 (q : Pattern) (selected : d2420 q = 0) : d53533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2420, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2420, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2421 q = 0) : d53534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2421, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2421, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2422 q = 0) : d53535 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2422, d53535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2422, d53535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8155 q = 0) : d84458 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8155, d84458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8155, d84458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8156 q = 0) : d84459 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8156, d84459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8156, d84459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4833 (p : Pattern) (selected : d8162 p = 0) : d84469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8157 q = 0) : d84460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8157, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4832 q selected
    | true =>
      simp only [d8157, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8158 q = 0) : d84461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8158, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8158, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2430 q = 0) : d53551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2430, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro628 q selected
    | true =>
      simp only [d2430, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2431 q = 0) : d53552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2431, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2431, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8159 q = 0) : d84466 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8159, d84466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8159, d84466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8160 q = 0) : d84467 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8160, d84467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8160, d84467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8161 q = 0) : d84468 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8161, d84468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8161, d84468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8162 q = 0) : d84469 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8162, d84469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8162, d84469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4834 (p : Pattern) (selected : d8168 p = 0) : d84476 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8144 q = 0) : d84460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4829 q selected
    | true =>
      simp only [d8144, d84460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8145 q = 0) : d84461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8145, d84461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8165 q = 0) : d84473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8165, d84473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8165, d84473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8166 q = 0) : d84474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8166, d84474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8166, d84474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8167 q = 0) : d84475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8167, d84475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8167, d84475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8168 q = 0) : d84476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8168, d84476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8168, d84476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4835 (p : Pattern) (selected : d8174 p = 0) : d84482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8154 q = 0) : d84470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8154, d84470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4830 q selected
    | true =>
      simp only [d8154, d84470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4831 q selected
  have h2 (q : Pattern) (selected : d8163 q = 0) : d84471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8163, d84471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4833 q selected
    | true =>
      simp only [d8163, d84471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro630 q selected
  have h3 (q : Pattern) (selected : d8164 q = 0) : d84472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8164, d84472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8164, d84472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8169 q = 0) : d84477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8169, d84477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4834 q selected
    | true =>
      simp only [d8169, d84477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8170 q = 0) : d84478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8170, d84478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8170, d84478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8171 q = 0) : d84479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8171, d84479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8171, d84479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8172 q = 0) : d84480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8172, d84480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8172, d84480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8173 q = 0) : d84481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8173, d84481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8173, d84481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8174 q = 0) : d84482 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8174, d84482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8174, d84482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4836 (p : Pattern) (selected : d8180 p = 0) : d84488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8050 q = 0) : d84377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d84377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8050, d84377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4809 q selected
  have h2 (q : Pattern) (selected : d8051 q = 0) : d84378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d84378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8051, d84378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8059 q = 0) : d84386 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d84386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4809 q selected
    | true =>
      simp only [d8059, d84386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4811 q selected
  have h4 (q : Pattern) (selected : d8060 q = 0) : d84387 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d84387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8060, d84387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8061 q = 0) : d84388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d84388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8061, d84388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8124 q = 0) : d84440 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8124, d84440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4819 q selected
    | true =>
      simp only [d8124, d84440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4825 q selected
  have h7 (q : Pattern) (selected : d8126 q = 0) : d84442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d84442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4826 q selected
    | true =>
      simp only [d8126, d84442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro612 q selected
  have h8 (q : Pattern) (selected : d8127 q = 0) : d84443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8127, d84443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8127, d84443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8128 q = 0) : d84444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8128, d84444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8128, d84444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d8129 q = 0) : d84445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8129, d84445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8129, d84445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8133 q = 0) : d84449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8133, d84449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8133, d84449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4827 q selected
  have h12 (q : Pattern) (selected : d2326 q = 0) : d53491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro614 q selected
  have h13 (q : Pattern) (selected : d8134 q = 0) : d84450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8134, d84450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8134, d84450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8135 q = 0) : d84451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8135, d84451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d8135, d84451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d8136 q = 0) : d84452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8136, d84452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d8136, d84452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d8137 q = 0) : d84453 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8137, d84453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8137, d84453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d8175 q = 0) : d84483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8175, d84483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8175, d84483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4835 q selected
  have h18 (q : Pattern) (selected : d2459 q = 0) : d53577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro633 q selected
  have h19 (q : Pattern) (selected : d8176 q = 0) : d84484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8176, d84484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8176, d84484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d8177 q = 0) : d84485 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8177, d84485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d8177, d84485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d8178 q = 0) : d84486 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8178, d84486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d8178, d84486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d8179 q = 0) : d84487 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8179, d84487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d8179, d84487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d8180 q = 0) : d84488 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d8180, d84488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d8180, d84488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4837 (p : Pattern) (selected : d8186 p = 0) : d84494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8181 q = 0) : d84489 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d8181, d84489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8181, d84489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4836 q selected
  have h2 (q : Pattern) (selected : d8182 q = 0) : d84490 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d8182, d84490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8182, d84490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8183 q = 0) : d84491 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d8183, d84491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8183, d84491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8184 q = 0) : d84492 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d8184, d84492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8184, d84492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8185 q = 0) : d84493 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d8185, d84493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8185, d84493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8186 q = 0) : d84494 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d8186, d84494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8186, d84494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4838 (p : Pattern) (selected : d8192 p = 0) : d84500 p = 1 := by
  have h0 (q : Pattern) (selected : d7573 q = 0) : d83957 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d7573, d83957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4684 q selected
    | true =>
      simp only [d7573, d83957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4713 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d7725 q = 0) : d84090 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d7725, d84090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7725, d84090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4744 q selected
  have h3 (q : Pattern) (selected : d7726 q = 0) : d84091 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d7726, d84091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7726, d84091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7878 q = 0) : d84224 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d7878, d84224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7878, d84224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4775 q selected
  have h5 (q : Pattern) (selected : d7879 q = 0) : d84225 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d7879, d84225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7879, d84225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7880 q = 0) : d84226 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d7880, d84226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7880, d84226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8032 q = 0) : d84359 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d8032, d84359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8032, d84359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4806 q selected
  have h8 (q : Pattern) (selected : d8033 q = 0) : d84360 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d8033, d84360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8033, d84360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8034 q = 0) : d84361 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d8034, d84361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8034, d84361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8035 q = 0) : d84362 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d8035, d84362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8035, d84362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8187 q = 0) : d84495 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d8187, d84495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8187, d84495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4837 q selected
  have h12 (q : Pattern) (selected : d8188 q = 0) : d84496 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d8188, d84496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8188, d84496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d8189 q = 0) : d84497 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d8189, d84497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8189, d84497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8190 q = 0) : d84498 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d8190, d84498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8190, d84498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8191 q = 0) : d84499 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d8191, d84499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8191, d84499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8192 q = 0) : d84500 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d8192, d84500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d8192, d84500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro4839 (p : Pattern) (selected : d8198 p = 0) : d84506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8193 q = 0) : d84501 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d8193, d84501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4838 q selected
    | true =>
      simp only [d8193, d84501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8194 q = 0) : d84502 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d8194, d84502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8194, d84502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8195 q = 0) : d84503 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d8195, d84503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8195, d84503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8196 q = 0) : d84504 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d8196, d84504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8196, d84504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8197 q = 0) : d84505 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d8197, d84505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8197, d84505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8198 q = 0) : d84506 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d8198, d84506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8198, d84506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4840 (p : Pattern) (selected : d8204 p = 0) : d84512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8199 q = 0) : d84507 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d8199, d84507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4839 q selected
    | true =>
      simp only [d8199, d84507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8200 q = 0) : d84508 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d8200, d84508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8200, d84508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8201 q = 0) : d84509 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d8201, d84509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8201, d84509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8202 q = 0) : d84510 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d8202, d84510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8202, d84510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8203 q = 0) : d84511 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d8203, d84511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8203, d84511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8204 q = 0) : d84512 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d8204, d84512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8204, d84512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4841 (p : Pattern) (selected : d8210 p = 0) : d84518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8205 q = 0) : d84513 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d8205, d84513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4840 q selected
    | true =>
      simp only [d8205, d84513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8206 q = 0) : d84514 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d8206, d84514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8206, d84514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8207 q = 0) : d84515 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d8207, d84515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8207, d84515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8208 q = 0) : d84516 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d8208, d84516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8208, d84516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8209 q = 0) : d84517 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d8209, d84517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8209, d84517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8210 q = 0) : d84518 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d8210, d84518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8210, d84518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4842 (p : Pattern) (selected : d8216 p = 0) : d84524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8211 q = 0) : d84519 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d8211, d84519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4841 q selected
    | true =>
      simp only [d8211, d84519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8212 q = 0) : d84520 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d8212, d84520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8212, d84520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8213 q = 0) : d84521 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d8213, d84521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8213, d84521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8214 q = 0) : d84522 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d8214, d84522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8214, d84522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8215 q = 0) : d84523 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d8215, d84523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8215, d84523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8216 q = 0) : d84524 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d8216, d84524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8216, d84524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4843 (p : Pattern) (selected : d8222 p = 0) : d84530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8217 q = 0) : d84525 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d8217, d84525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4842 q selected
    | true =>
      simp only [d8217, d84525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8218 q = 0) : d84526 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d8218, d84526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8218, d84526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8219 q = 0) : d84527 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d8219, d84527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8219, d84527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8220 q = 0) : d84528 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d8220, d84528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8220, d84528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8221 q = 0) : d84529 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d8221, d84529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8221, d84529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8222 q = 0) : d84530 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d8222, d84530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8222, d84530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4844 (p : Pattern) (selected : d8228 p = 0) : d84536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8223 q = 0) : d84531 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d8223, d84531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4843 q selected
    | true =>
      simp only [d8223, d84531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8224 q = 0) : d84532 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d8224, d84532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8224, d84532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8225 q = 0) : d84533 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d8225, d84533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8225, d84533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8226 q = 0) : d84534 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d8226, d84534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8226, d84534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8227 q = 0) : d84535 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d8227, d84535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8227, d84535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8228 q = 0) : d84536 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d8228, d84536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8228, d84536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4845 (p : Pattern) (selected : d8234 p = 0) : d84542 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d8229 q = 0) : d84537 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d8229, d84537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4844 q selected
    | true =>
      simp only [d8229, d84537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8230 q = 0) : d84538 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d8230, d84538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8230, d84538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8231 q = 0) : d84539 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d8231, d84539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8231, d84539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8232 q = 0) : d84540 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d8232, d84540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8232, d84540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8233 q = 0) : d84541 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d8233, d84541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8233, d84541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8234 q = 0) : d84542 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d8234, d84542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8234, d84542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4846 (p : Pattern) (selected : d7253 p = 1) : d85394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7248 q = 1) : d7248 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d7249 q = 1) : d85390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7249, d85390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7249, d85390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d7250 q = 1) : d85391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7250, d85391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7250, d85391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7251 q = 1) : d85392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7251, d85392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7251, d85392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7252 q = 1) : d85393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7252, d85393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7252, d85393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7253 q = 1) : d85394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7253, d85394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7253, d85394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro4847 (p : Pattern) (selected : d7260 p = 1) : d85399 p = 1 := by
  have h0 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7248 q = 1) : d7248 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7249 q = 1) : d85390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7249, d85390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7249, d85390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d7250 q = 1) : d85391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7250, d85391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7250, d85391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7251 q = 1) : d85392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7251, d85392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7251, d85392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7252 q = 1) : d85393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7252, d85393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7252, d85393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d198 q = 1) : d198 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d202 q = 1) : d202 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d7255 q = 1) : d7255 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d7256 q = 1) : d85395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7256, d85395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7256, d85395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d7257 q = 1) : d85396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7257, d85396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7257, d85396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7258 q = 1) : d85397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7258, d85397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7258, d85397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7259 q = 1) : d85398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7259, d85398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7259, d85398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d7260 q = 1) : d85399 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7260, d85399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7260, d85399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro4848 (p : Pattern) (selected : d7267 p = 1) : d85406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7255 q = 1) : d7255 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7256 q = 1) : d85395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7256, d85395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7256, d85395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7257 q = 1) : d85396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7257, d85396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7257, d85396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7265 q = 1) : d85404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7265, d85404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7265, d85404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7266 q = 1) : d85405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7266, d85405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7266, d85405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7267 q = 1) : d85406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7267, d85406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7267, d85406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4849 (p : Pattern) (selected : d7286 p = 1) : d85416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7281 q = 1) : d7281 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
    | true =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d7282 q = 1) : d85412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7282, d85412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7282, d85412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85 q = 1) : d85 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7283 q = 1) : d85413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7283, d85413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7283, d85413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7284 q = 1) : d85414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7284, d85414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7284, d85414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7285 q = 1) : d85415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7285, d85415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7285, d85415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7286 q = 1) : d85416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7286, d85416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7286, d85416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4850 (p : Pattern) (selected : d7292 p = 1) : d85422 p = 1 := by
  have h0 (q : Pattern) (selected : d114 q = 1) : d114 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7261 q = 1) : d85400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7261, d85400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4846 q selected
    | true =>
      simp only [d7261, d85400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4847 q selected
  have h2 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7262 q = 1) : d85401 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7262, d85401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7262, d85401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7263 q = 1) : d85402 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7263, d85402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7263, d85402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7264 q = 1) : d85403 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7264, d85403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7264, d85403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7268 q = 1) : d85407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7268, d85407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7268, d85407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4848 q selected
  have h8 (q : Pattern) (selected : d7269 q = 1) : d85408 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7269, d85408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7269, d85408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d7270 q = 1) : d85409 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7270, d85409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7270, d85409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d7271 q = 1) : d85410 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7271, d85410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7271, d85410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d7272 q = 1) : d85411 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7272, d85411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7272, d85411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d7287 q = 1) : d85417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7287, d85417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7287, d85417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4849 q selected
  have h13 (q : Pattern) (selected : d7288 q = 1) : d85418 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7288, d85418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7288, d85418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d7289 q = 1) : d85419 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7289, d85419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7289, d85419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d7290 q = 1) : d85420 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7290, d85420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d7290, d85420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d7291 q = 1) : d85421 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7291, d85421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7291, d85421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d7292 q = 1) : d85422 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7292, d85422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7292, d85422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro4851 (p : Pattern) (selected : d7335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
    | true =>
      simp only [d356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h2 (q : Pattern) (selected : d357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
    | true =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7334 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7335 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4852 (p : Pattern) (selected : d7341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4851 q selected
    | true =>
      simp only [d7336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7338 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7341 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4853 (p : Pattern) (selected : d7353 p = 1) : d85432 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7318 q = 1) : d7318 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7324 q = 1) : d7324 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7333 q = 1) : d7333 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d7342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4852 q selected
    | true =>
      simp only [d7342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h5 (q : Pattern) (selected : d7343 q = 1) : d85428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7343, d85428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7343, d85428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7349 q = 1) : d7349 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d7350 q = 1) : d85429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7350, d85429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7350, d85429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7351 q = 1) : d85430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7351, d85430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7351, d85430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7352 q = 1) : d85431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7352, d85431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7352, d85431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7353 q = 1) : d85432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7353, d85432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7353, d85432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro4854 (p : Pattern) (selected : d7365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4851 q selected
    | true =>
      simp only [d7336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7338 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7365 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4855 (p : Pattern) (selected : d7374 p = 1) : d85437 p = 1 := by
  have h0 (q : Pattern) (selected : d7318 q = 1) : d7318 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7324 q = 1) : d7324 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7333 q = 1) : d7333 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7342 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4852 q selected
    | true =>
      simp only [d7342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d7343 q = 1) : d85428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7343, d85428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7343, d85428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7349 q = 1) : d7349 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d7350 q = 1) : d85429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7350, d85429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7350, d85429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7351 q = 1) : d85430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7351, d85430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7351, d85430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7352 q = 1) : d85431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7352, d85431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7352, d85431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7358 q = 1) : d7358 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d7362 q = 1) : d7362 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d7364 q = 1) : d7364 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d7366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4854 q selected
    | true =>
      simp only [d7366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h13 (q : Pattern) (selected : d7367 q = 1) : d85433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7367, d85433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7367, d85433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7370 q = 1) : d7370 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7371 q = 1) : d85434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7371, d85434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7371, d85434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7372 q = 1) : d85435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7372, d85435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7372, d85435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7373 q = 1) : d85436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7373, d85436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7373, d85436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7374 q = 1) : d85437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7374, d85437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7374, d85437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro4856 (p : Pattern) (selected : d7383 p = 1) : d85444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7364 q = 1) : d7364 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4854 q selected
    | true =>
      simp only [d7366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h3 (q : Pattern) (selected : d7367 q = 1) : d85433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7367, d85433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7367, d85433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7370 q = 1) : d7370 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7371 q = 1) : d85434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7371, d85434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7371, d85434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7381 q = 1) : d85442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7381, d85442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7381, d85442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7382 q = 1) : d85443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7382, d85443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7382, d85443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7383 q = 1) : d85444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7383, d85444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7383, d85444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4857 (p : Pattern) (selected : d7399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h2 (q : Pattern) (selected : d438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
    | true =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d440 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7398 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7399 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4858 (p : Pattern) (selected : d7405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7400 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4857 q selected
    | true =>
      simp only [d7400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7401 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10 q selected
    | true =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7402 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4859 (p : Pattern) (selected : d7417 p = 1) : d85454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7397 q = 1) : d7397 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4858 q selected
    | true =>
      simp only [d7406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
  have h3 (q : Pattern) (selected : d7407 q = 1) : d85450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7407, d85450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7407, d85450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7413 q = 1) : d7413 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7414 q = 1) : d85451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7414, d85451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7414, d85451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7415 q = 1) : d85452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7415, d85452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7415, d85452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7416 q = 1) : d85453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7416, d85453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7416, d85453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7417 q = 1) : d85454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7417, d85454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7417, d85454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4860 (p : Pattern) (selected : d7423 p = 1) : d85460 p = 1 := by
  have h0 (q : Pattern) (selected : d7312 q = 1) : d7312 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7375 q = 1) : d85438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7375, d85438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4853 q selected
    | true =>
      simp only [d7375, d85438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4855 q selected
  have h2 (q : Pattern) (selected : d7377 q = 1) : d7377 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7378 q = 1) : d85439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7378, d85439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7378, d85439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7379 q = 1) : d85440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7379, d85440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7379, d85440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7380 q = 1) : d85441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7380, d85441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7380, d85441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7384 q = 1) : d85445 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7384, d85445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7384, d85445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4856 q selected
  have h8 (q : Pattern) (selected : d407 q = 1) : d407 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d7385 q = 1) : d85446 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7385, d85446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7385, d85446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7386 q = 1) : d85447 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7386, d85447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7386, d85447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d7387 q = 1) : d85448 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7387, d85448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7387, d85448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d7388 q = 1) : d85449 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7388, d85449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7388, d85449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d7418 q = 1) : d85455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7418, d85455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7418, d85455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4859 q selected
  have h14 (q : Pattern) (selected : d463 q = 1) : d463 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7419 q = 1) : d85456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7419, d85456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7419, d85456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7420 q = 1) : d85457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7420, d85457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7420, d85457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d7421 q = 1) : d85458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7421, d85458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7421, d85458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d7422 q = 1) : d85459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7422, d85459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7422, d85459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d7423 q = 1) : d85460 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7423, d85460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7423, d85460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro4861 (p : Pattern) (selected : d7429 p = 1) : d85466 p = 1 := by
  have h0 (q : Pattern) (selected : d99 q = 1) : d99 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7293 q = 1) : d85423 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7293, d85423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7293, d85423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4850 q selected
  have h3 (q : Pattern) (selected : d7294 q = 1) : d85424 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7294, d85424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7294, d85424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7295 q = 1) : d85425 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7295, d85425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7295, d85425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7296 q = 1) : d85426 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7296, d85426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7296, d85426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7297 q = 1) : d85427 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7297, d85427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7297, d85427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7424 q = 1) : d85461 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7424, d85461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7424, d85461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4860 q selected
  have h8 (q : Pattern) (selected : d7425 q = 1) : d85462 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7425, d85462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7425, d85462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7426 q = 1) : d85463 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7426, d85463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7426, d85463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7427 q = 1) : d85464 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7427, d85464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7427, d85464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d7428 q = 1) : d85465 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7428, d85465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7428, d85465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d7429 q = 1) : d85466 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7429, d85466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7429, d85466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro4862 (p : Pattern) (selected : d7474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d580 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31 q selected
    | true =>
      simp only [d580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
  have h2 (q : Pattern) (selected : d581 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d582 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
    | true =>
      simp only [d356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h5 (q : Pattern) (selected : d357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d583 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7473 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7474 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4863 (p : Pattern) (selected : d7480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4862 q selected
    | true =>
      simp only [d7475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33 q selected
    | true =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7477 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7478 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7479 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7480 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4864 (p : Pattern) (selected : d7492 p = 1) : d85471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7457 q = 1) : d7457 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7463 q = 1) : d7463 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7472 q = 1) : d7472 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d7481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4863 q selected
    | true =>
      simp only [d7481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h5 (q : Pattern) (selected : d7482 q = 1) : d85467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7482, d85467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7482, d85467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7488 q = 1) : d7488 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d7489 q = 1) : d85468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7489, d85468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7489, d85468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7490 q = 1) : d85469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7490, d85469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7490, d85469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7491 q = 1) : d85470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7491, d85470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7491, d85470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7492 q = 1) : d85471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7492, d85471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7492, d85471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro4865 (p : Pattern) (selected : d7504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4862 q selected
    | true =>
      simp only [d7475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33 q selected
    | true =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7477 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7478 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7479 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4866 (p : Pattern) (selected : d7513 p = 1) : d85476 p = 1 := by
  have h0 (q : Pattern) (selected : d7457 q = 1) : d7457 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7463 q = 1) : d7463 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7472 q = 1) : d7472 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4863 q selected
    | true =>
      simp only [d7481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h4 (q : Pattern) (selected : d7482 q = 1) : d85467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7482, d85467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7482, d85467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7488 q = 1) : d7488 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d7489 q = 1) : d85468 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7489, d85468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7489, d85468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7490 q = 1) : d85469 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7490, d85469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7490, d85469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7491 q = 1) : d85470 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7491, d85470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7491, d85470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7497 q = 1) : d7497 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d7501 q = 1) : d7501 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d7503 q = 1) : d7503 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d7505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4865 q selected
    | true =>
      simp only [d7505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h13 (q : Pattern) (selected : d7506 q = 1) : d85472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7506, d85472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7506, d85472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7509 q = 1) : d7509 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7510 q = 1) : d85473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7510, d85473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7510, d85473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7511 q = 1) : d85474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7511, d85474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7511, d85474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7512 q = 1) : d85475 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7512, d85475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7512, d85475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7513 q = 1) : d85476 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7513, d85476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7513, d85476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro4867 (p : Pattern) (selected : d7522 p = 1) : d85483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7503 q = 1) : d7503 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4865 q selected
    | true =>
      simp only [d7505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h3 (q : Pattern) (selected : d7506 q = 1) : d85472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7506, d85472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7506, d85472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7509 q = 1) : d7509 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7510 q = 1) : d85473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7510, d85473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7510, d85473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7520 q = 1) : d85481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7520, d85481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7520, d85481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7521 q = 1) : d85482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7521, d85482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7521, d85482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7522 q = 1) : d85483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7522, d85483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7522, d85483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4868 (p : Pattern) (selected : d7542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d697 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro41 q selected
    | true =>
      simp only [d697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
  have h2 (q : Pattern) (selected : d698 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d699 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h5 (q : Pattern) (selected : d438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d700 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4869 (p : Pattern) (selected : d7548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4868 q selected
    | true =>
      simp only [d7543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro43 q selected
    | true =>
      simp only [d708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4870 (p : Pattern) (selected : d7560 p = 1) : d85493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7540 q = 1) : d7540 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4869 q selected
    | true =>
      simp only [d7549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro45 q selected
  have h3 (q : Pattern) (selected : d7550 q = 1) : d85489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7550, d85489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7550, d85489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7556 q = 1) : d7556 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7557 q = 1) : d85490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7557, d85490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7557, d85490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7558 q = 1) : d85491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7558, d85491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7558, d85491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7559 q = 1) : d85492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7559, d85492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7559, d85492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7560 q = 1) : d85493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7560, d85493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7560, d85493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4871 (p : Pattern) (selected : d7566 p = 1) : d85499 p = 1 := by
  have h0 (q : Pattern) (selected : d7451 q = 1) : d7451 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7514 q = 1) : d85477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7514, d85477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4864 q selected
    | true =>
      simp only [d7514, d85477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4866 q selected
  have h2 (q : Pattern) (selected : d7516 q = 1) : d7516 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7517 q = 1) : d85478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7517, d85478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7517, d85478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7518 q = 1) : d85479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7518, d85479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7518, d85479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7519 q = 1) : d85480 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7519, d85480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7519, d85480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7523 q = 1) : d85484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7523, d85484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7523, d85484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4867 q selected
  have h8 (q : Pattern) (selected : d654 q = 1) : d654 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d7524 q = 1) : d85485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7524, d85485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7524, d85485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7525 q = 1) : d85486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7525, d85486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7525, d85486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d7526 q = 1) : d85487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7526, d85487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7526, d85487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d7527 q = 1) : d85488 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7527, d85488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7527, d85488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d7561 q = 1) : d85494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7561, d85494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7561, d85494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4870 q selected
  have h14 (q : Pattern) (selected : d737 q = 1) : d737 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7562 q = 1) : d85495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7562, d85495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7562, d85495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7563 q = 1) : d85496 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7563, d85496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7563, d85496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d7564 q = 1) : d85497 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7564, d85497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7564, d85497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d7565 q = 1) : d85498 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7565, d85498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7565, d85498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d7566 q = 1) : d85499 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7566, d85499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7566, d85499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro4872 (p : Pattern) (selected : d7572 p = 1) : d85505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7567 q = 1) : d85500 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7567, d85500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7567, d85500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4871 q selected
  have h2 (q : Pattern) (selected : d7568 q = 1) : d85501 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7568, d85501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7568, d85501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7569 q = 1) : d85502 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7569, d85502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7569, d85502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7570 q = 1) : d85503 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7570, d85503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7570, d85503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7571 q = 1) : d85504 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7571, d85504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7571, d85504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7572 q = 1) : d85505 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7572, d85505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7572, d85505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4873 (p : Pattern) (selected : d7622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d882 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro53 q selected
    | true =>
      simp only [d882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro54 q selected
  have h2 (q : Pattern) (selected : d883 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d884 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro54 q selected
    | true =>
      simp only [d886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro55 q selected
  have h5 (q : Pattern) (selected : d887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d889 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7621 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7622 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4874 (p : Pattern) (selected : d7628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4873 q selected
    | true =>
      simp only [d7623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro57 q selected
    | true =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4875 (p : Pattern) (selected : d7640 p = 1) : d85511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7605 q = 1) : d7605 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7611 q = 1) : d7611 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7620 q = 1) : d7620 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d7629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4874 q selected
    | true =>
      simp only [d7629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h5 (q : Pattern) (selected : d7630 q = 1) : d85507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7630, d85507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7630, d85507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7636 q = 1) : d7636 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d7637 q = 1) : d85508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7637, d85508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7637, d85508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7638 q = 1) : d85509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7638, d85509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7638, d85509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7639 q = 1) : d85510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7639, d85510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7639, d85510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7640 q = 1) : d85511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7640, d85511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7640, d85511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro4876 (p : Pattern) (selected : d7652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4873 q selected
    | true =>
      simp only [d7623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro57 q selected
    | true =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7652 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4877 (p : Pattern) (selected : d7661 p = 1) : d85516 p = 1 := by
  have h0 (q : Pattern) (selected : d7605 q = 1) : d7605 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7611 q = 1) : d7611 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7620 q = 1) : d7620 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4874 q selected
    | true =>
      simp only [d7629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h4 (q : Pattern) (selected : d7630 q = 1) : d85507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7630, d85507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7630, d85507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7636 q = 1) : d7636 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d7637 q = 1) : d85508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7637, d85508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7637, d85508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7638 q = 1) : d85509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7638, d85509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7638, d85509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7639 q = 1) : d85510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7639, d85510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7639, d85510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7645 q = 1) : d7645 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d7649 q = 1) : d7649 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d7651 q = 1) : d7651 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d7653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4876 q selected
    | true =>
      simp only [d7653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h13 (q : Pattern) (selected : d7654 q = 1) : d85512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7654, d85512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7654, d85512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7657 q = 1) : d7657 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7658 q = 1) : d85513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7658, d85513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7658, d85513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7659 q = 1) : d85514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7659, d85514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7659, d85514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7660 q = 1) : d85515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7660, d85515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7660, d85515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7661 q = 1) : d85516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7661, d85516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7661, d85516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro4878 (p : Pattern) (selected : d7670 p = 1) : d85523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7651 q = 1) : d7651 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7653 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4876 q selected
    | true =>
      simp only [d7653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h3 (q : Pattern) (selected : d7654 q = 1) : d85512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7654, d85512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7654, d85512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7657 q = 1) : d7657 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7658 q = 1) : d85513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7658, d85513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7658, d85513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7668 q = 1) : d85521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7668, d85521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7668, d85521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7669 q = 1) : d85522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7669, d85522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7669, d85522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7670 q = 1) : d85523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7670, d85523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7670, d85523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4879 (p : Pattern) (selected : d7694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1026 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro65 q selected
    | true =>
      simp only [d1026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
  have h2 (q : Pattern) (selected : d1027 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1028 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1030 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
    | true =>
      simp only [d1030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro67 q selected
  have h5 (q : Pattern) (selected : d1031 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1032 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1033 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7693 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7694 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4880 (p : Pattern) (selected : d7700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4879 q selected
    | true =>
      simp only [d7695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1041 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro69 q selected
    | true =>
      simp only [d1041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1042 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7697 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4881 (p : Pattern) (selected : d7712 p = 1) : d85533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7692 q = 1) : d7692 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4880 q selected
    | true =>
      simp only [d7701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro71 q selected
  have h3 (q : Pattern) (selected : d7702 q = 1) : d85529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7702, d85529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7702, d85529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7708 q = 1) : d7708 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7709 q = 1) : d85530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7709, d85530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7709, d85530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7710 q = 1) : d85531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7710, d85531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7710, d85531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7711 q = 1) : d85532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7711, d85532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7711, d85532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7712 q = 1) : d85533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7712, d85533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7712, d85533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4882 (p : Pattern) (selected : d7718 p = 1) : d85539 p = 1 := by
  have h0 (q : Pattern) (selected : d7599 q = 1) : d7599 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7662 q = 1) : d85517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7662, d85517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4875 q selected
    | true =>
      simp only [d7662, d85517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4877 q selected
  have h2 (q : Pattern) (selected : d7664 q = 1) : d7664 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7665 q = 1) : d85518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7665, d85518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7665, d85518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7666 q = 1) : d85519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7666, d85519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7666, d85519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7667 q = 1) : d85520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7667, d85520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7667, d85520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7671 q = 1) : d85524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7671, d85524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7671, d85524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4878 q selected
  have h8 (q : Pattern) (selected : d960 q = 1) : d960 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d7672 q = 1) : d85525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7672, d85525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7672, d85525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7673 q = 1) : d85526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7673, d85526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7673, d85526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d7674 q = 1) : d85527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7674, d85527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7674, d85527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d7675 q = 1) : d85528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7675, d85528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7675, d85528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d7713 q = 1) : d85534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7713, d85534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7713, d85534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4881 q selected
  have h14 (q : Pattern) (selected : d1070 q = 1) : d1070 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7714 q = 1) : d85535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7714, d85535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7714, d85535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7715 q = 1) : d85536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7715, d85536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7715, d85536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d7716 q = 1) : d85537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7716, d85537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7716, d85537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d7717 q = 1) : d85538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7717, d85538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7717, d85538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d7718 q = 1) : d85539 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7718, d85539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7718, d85539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro4883 (p : Pattern) (selected : d7724 p = 1) : d85545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7719 q = 1) : d85540 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7719, d85540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7719, d85540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4882 q selected
  have h2 (q : Pattern) (selected : d7720 q = 1) : d85541 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7720, d85541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7720, d85541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7721 q = 1) : d85542 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7721, d85542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7721, d85542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7722 q = 1) : d85543 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7722, d85543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7722, d85543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7723 q = 1) : d85544 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7723, d85544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7723, d85544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7724 q = 1) : d85545 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7724, d85545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7724, d85545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4884 (p : Pattern) (selected : d7775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1284 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro82 q selected
    | true =>
      simp only [d1284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro83 q selected
  have h2 (q : Pattern) (selected : d1285 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1286 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1297 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro83 q selected
    | true =>
      simp only [d1297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro85 q selected
  have h5 (q : Pattern) (selected : d1298 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1299 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1300 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7775 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4885 (p : Pattern) (selected : d7781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7776 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4884 q selected
    | true =>
      simp only [d7776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7777 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro87 q selected
    | true =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7778 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7779 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7780 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7781 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4886 (p : Pattern) (selected : d7793 p = 1) : d85552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7758 q = 1) : d7758 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7764 q = 1) : d7764 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7773 q = 1) : d7773 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d7782 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4885 q selected
    | true =>
      simp only [d7782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h5 (q : Pattern) (selected : d7783 q = 1) : d85548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7783, d85548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7783, d85548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7789 q = 1) : d7789 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d7790 q = 1) : d85549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7790, d85549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7790, d85549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7791 q = 1) : d85550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7791, d85550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7791, d85550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7792 q = 1) : d85551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7792, d85551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7792, d85551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7793 q = 1) : d85552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7793, d85552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7793, d85552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro4887 (p : Pattern) (selected : d7805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7776 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4884 q selected
    | true =>
      simp only [d7776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7777 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro87 q selected
    | true =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7778 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7779 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7780 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7805 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4888 (p : Pattern) (selected : d7814 p = 1) : d85557 p = 1 := by
  have h0 (q : Pattern) (selected : d7758 q = 1) : d7758 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7764 q = 1) : d7764 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7773 q = 1) : d7773 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7782 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4885 q selected
    | true =>
      simp only [d7782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h4 (q : Pattern) (selected : d7783 q = 1) : d85548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7783, d85548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7783, d85548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7789 q = 1) : d7789 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d7790 q = 1) : d85549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7790, d85549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7790, d85549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7791 q = 1) : d85550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7791, d85550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7791, d85550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7792 q = 1) : d85551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7792, d85551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7792, d85551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7798 q = 1) : d7798 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d7802 q = 1) : d7802 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d7804 q = 1) : d7804 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d7806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4887 q selected
    | true =>
      simp only [d7806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h13 (q : Pattern) (selected : d7807 q = 1) : d85553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7807, d85553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7807, d85553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7810 q = 1) : d7810 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7811 q = 1) : d85554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7811, d85554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7811, d85554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7812 q = 1) : d85555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7812, d85555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7812, d85555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7813 q = 1) : d85556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7813, d85556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7813, d85556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7814 q = 1) : d85557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7814, d85557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7814, d85557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro4889 (p : Pattern) (selected : d7823 p = 1) : d85564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7804 q = 1) : d7804 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4887 q selected
    | true =>
      simp only [d7806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h3 (q : Pattern) (selected : d7807 q = 1) : d85553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7807, d85553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7807, d85553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7810 q = 1) : d7810 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7811 q = 1) : d85554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7811, d85554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7811, d85554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7821 q = 1) : d85562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7821, d85562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7821, d85562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7822 q = 1) : d85563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7822, d85563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7822, d85563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7823 q = 1) : d85564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7823, d85564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7823, d85564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4890 (p : Pattern) (selected : d7847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1455 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro95 q selected
    | true =>
      simp only [d1455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro96 q selected
  have h2 (q : Pattern) (selected : d1456 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1457 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro96 q selected
    | true =>
      simp only [d1464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro97 q selected
  have h5 (q : Pattern) (selected : d1465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1467 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7846 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7847 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4891 (p : Pattern) (selected : d7853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4890 q selected
    | true =>
      simp only [d7848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro99 q selected
    | true =>
      simp only [d1475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4892 (p : Pattern) (selected : d7865 p = 1) : d85574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7845 q = 1) : d7845 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4891 q selected
    | true =>
      simp only [d7854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro101 q selected
  have h3 (q : Pattern) (selected : d7855 q = 1) : d85570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7855, d85570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7855, d85570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7861 q = 1) : d7861 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7862 q = 1) : d85571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7862, d85571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7862, d85571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7863 q = 1) : d85572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7863, d85572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7863, d85572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7864 q = 1) : d85573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7864, d85573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7864, d85573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7865 q = 1) : d85574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7865, d85574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7865, d85574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4893 (p : Pattern) (selected : d7871 p = 1) : d85580 p = 1 := by
  have h0 (q : Pattern) (selected : d7752 q = 1) : d7752 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7815 q = 1) : d85558 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7815, d85558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4886 q selected
    | true =>
      simp only [d7815, d85558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4888 q selected
  have h2 (q : Pattern) (selected : d7817 q = 1) : d7817 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7818 q = 1) : d85559 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7818, d85559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7818, d85559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7819 q = 1) : d85560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7819, d85560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7819, d85560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7820 q = 1) : d85561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7820, d85561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7820, d85561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7824 q = 1) : d85565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7824, d85565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7824, d85565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4889 q selected
  have h8 (q : Pattern) (selected : d1371 q = 1) : d1371 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d7825 q = 1) : d85566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7825, d85566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7825, d85566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7826 q = 1) : d85567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7826, d85567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7826, d85567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d7827 q = 1) : d85568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7827, d85568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7827, d85568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d7828 q = 1) : d85569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7828, d85569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7828, d85569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d7866 q = 1) : d85575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7866, d85575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7866, d85575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4892 q selected
  have h14 (q : Pattern) (selected : d1504 q = 1) : d1504 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7867 q = 1) : d85576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7867, d85576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7867, d85576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7868 q = 1) : d85577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7868, d85577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d7868, d85577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d7869 q = 1) : d85578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7869, d85578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d7869, d85578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d7870 q = 1) : d85579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7870, d85579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d7870, d85579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d7871 q = 1) : d85580 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d7871, d85580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d7871, d85580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro4894 (p : Pattern) (selected : d7877 p = 1) : d85586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7872 q = 1) : d85581 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d7872, d85581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7872, d85581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4893 q selected
  have h2 (q : Pattern) (selected : d7873 q = 1) : d85582 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d7873, d85582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7873, d85582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d7874 q = 1) : d85583 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d7874, d85583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7874, d85583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7875 q = 1) : d85584 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d7875, d85584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7875, d85584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7876 q = 1) : d85585 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d7876, d85585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7876, d85585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7877 q = 1) : d85586 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d7877, d85586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7877, d85586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4895 (p : Pattern) (selected : d7929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1761 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro118 q selected
    | true =>
      simp only [d1761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro119 q selected
  have h2 (q : Pattern) (selected : d1762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1763 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1774 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro119 q selected
    | true =>
      simp only [d1774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro121 q selected
  have h5 (q : Pattern) (selected : d1775 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1776 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1777 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7928 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d7929 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4896 (p : Pattern) (selected : d7935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4895 q selected
    | true =>
      simp only [d7930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro123 q selected
    | true =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4897 (p : Pattern) (selected : d7947 p = 1) : d85594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7912 q = 1) : d7912 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7918 q = 1) : d7918 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7927 q = 1) : d7927 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d7936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4896 q selected
    | true =>
      simp only [d7936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h5 (q : Pattern) (selected : d7937 q = 1) : d85590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7937, d85590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7937, d85590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7943 q = 1) : d7943 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d7944 q = 1) : d85591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7944, d85591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7944, d85591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7945 q = 1) : d85592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7945, d85592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7945, d85592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7946 q = 1) : d85593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7946, d85593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7946, d85593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7947 q = 1) : d85594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7947, d85594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7947, d85594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro4898 (p : Pattern) (selected : d7959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4895 q selected
    | true =>
      simp only [d7930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro123 q selected
    | true =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7932 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d7933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d7934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d7959 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4899 (p : Pattern) (selected : d7968 p = 1) : d85599 p = 1 := by
  have h0 (q : Pattern) (selected : d7912 q = 1) : d7912 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7918 q = 1) : d7918 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7927 q = 1) : d7927 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4896 q selected
    | true =>
      simp only [d7936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h4 (q : Pattern) (selected : d7937 q = 1) : d85590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7937, d85590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d7937, d85590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d7943 q = 1) : d7943 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d7944 q = 1) : d85591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7944, d85591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7944, d85591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7945 q = 1) : d85592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7945, d85592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7945, d85592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7946 q = 1) : d85593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7946, d85593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7946, d85593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d7952 q = 1) : d7952 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d7956 q = 1) : d7956 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d7958 q = 1) : d7958 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d7960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4898 q selected
    | true =>
      simp only [d7960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h13 (q : Pattern) (selected : d7961 q = 1) : d85595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7961, d85595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d7961, d85595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d7964 q = 1) : d7964 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d7965 q = 1) : d85596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7965, d85596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d7965, d85596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d7966 q = 1) : d85597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7966, d85597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7966, d85597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d7967 q = 1) : d85598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7967, d85598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7967, d85598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d7968 q = 1) : d85599 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7968, d85599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d7968, d85599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro4900 (p : Pattern) (selected : d7977 p = 1) : d85606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7958 q = 1) : d7958 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4898 q selected
    | true =>
      simp only [d7960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h3 (q : Pattern) (selected : d7961 q = 1) : d85595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7961, d85595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7961, d85595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7964 q = 1) : d7964 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7965 q = 1) : d85596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7965, d85596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7965, d85596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7975 q = 1) : d85604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7975, d85604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7975, d85604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7976 q = 1) : d85605 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7976, d85605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7976, d85605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d7977 q = 1) : d85606 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7977, d85606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7977, d85606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4901 (p : Pattern) (selected : d8001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro131 q selected
    | true =>
      simp only [d1932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro132 q selected
  have h2 (q : Pattern) (selected : d1933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1941 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro132 q selected
    | true =>
      simp only [d1941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro133 q selected
  have h5 (q : Pattern) (selected : d1942 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1943 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1944 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8000 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4902 (p : Pattern) (selected : d8007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4901 q selected
    | true =>
      simp only [d8002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1952 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro135 q selected
    | true =>
      simp only [d1952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1953 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4903 (p : Pattern) (selected : d8019 p = 1) : d85616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7999 q = 1) : d7999 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d8008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4902 q selected
    | true =>
      simp only [d8008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro137 q selected
  have h3 (q : Pattern) (selected : d8009 q = 1) : d85612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8009, d85612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8009, d85612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8015 q = 1) : d8015 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d8016 q = 1) : d85613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8016, d85613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8016, d85613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8017 q = 1) : d85614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8017, d85614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8017, d85614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8018 q = 1) : d85615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8018, d85615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8018, d85615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8019 q = 1) : d85616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8019, d85616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8019, d85616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4904 (p : Pattern) (selected : d8025 p = 1) : d85622 p = 1 := by
  have h0 (q : Pattern) (selected : d7906 q = 1) : d7906 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d7969 q = 1) : d85600 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7969, d85600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4897 q selected
    | true =>
      simp only [d7969, d85600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4899 q selected
  have h2 (q : Pattern) (selected : d7971 q = 1) : d7971 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d7972 q = 1) : d85601 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7972, d85601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7972, d85601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d7973 q = 1) : d85602 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7973, d85602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7973, d85602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7974 q = 1) : d85603 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7974, d85603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7974, d85603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d7978 q = 1) : d85607 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7978, d85607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d7978, d85607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4900 q selected
  have h8 (q : Pattern) (selected : d1848 q = 1) : d1848 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d7979 q = 1) : d85608 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7979, d85608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d7979, d85608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d7980 q = 1) : d85609 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7980, d85609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d7980, d85609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d7981 q = 1) : d85610 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d7981, d85610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d7981, d85610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d7982 q = 1) : d85611 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d7982, d85611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d7982, d85611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d8020 q = 1) : d85617 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8020, d85617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8020, d85617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4903 q selected
  have h14 (q : Pattern) (selected : d1981 q = 1) : d1981 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d8021 q = 1) : d85618 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8021, d85618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d8021, d85618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8022 q = 1) : d85619 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8022, d85619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d8022, d85619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d8023 q = 1) : d85620 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8023, d85620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d8023, d85620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d8024 q = 1) : d85621 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8024, d85621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8024, d85621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d8025 q = 1) : d85622 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d8025, d85622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d8025, d85622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro4905 (p : Pattern) (selected : d8031 p = 1) : d85628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8026 q = 1) : d85623 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d8026, d85623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8026, d85623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4904 q selected
  have h2 (q : Pattern) (selected : d8027 q = 1) : d85624 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d8027, d85624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8027, d85624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8028 q = 1) : d85625 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d8028, d85625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8028, d85625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8029 q = 1) : d85626 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d8029, d85626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8029, d85626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8030 q = 1) : d85627 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d8030, d85627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8030, d85627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8031 q = 1) : d85628 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d8031, d85628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8031, d85628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4906 (p : Pattern) (selected : d8084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2239 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro155 q selected
    | true =>
      simp only [d2239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro156 q selected
  have h2 (q : Pattern) (selected : d2240 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2241 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2252 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro156 q selected
    | true =>
      simp only [d2252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro158 q selected
  have h5 (q : Pattern) (selected : d2253 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2254 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2255 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8083 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8084 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4907 (p : Pattern) (selected : d8090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4906 q selected
    | true =>
      simp only [d8085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro160 q selected
    | true =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8087 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8088 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8089 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4908 (p : Pattern) (selected : d8102 p = 1) : d85637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8067 q = 1) : d8067 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d8073 q = 1) : d8073 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d8082 q = 1) : d8082 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d8091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4907 q selected
    | true =>
      simp only [d8091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h5 (q : Pattern) (selected : d8092 q = 1) : d85633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8092, d85633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8092, d85633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8098 q = 1) : d8098 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d8099 q = 1) : d85634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8099, d85634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8099, d85634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8100 q = 1) : d85635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8100, d85635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8100, d85635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8101 q = 1) : d85636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8101, d85636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8101, d85636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8102 q = 1) : d85637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8102, d85637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8102, d85637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro4909 (p : Pattern) (selected : d8114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4906 q selected
    | true =>
      simp only [d8085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro160 q selected
    | true =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8087 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8088 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8089 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8114 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4910 (p : Pattern) (selected : d8123 p = 1) : d85642 p = 1 := by
  have h0 (q : Pattern) (selected : d8067 q = 1) : d8067 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8073 q = 1) : d8073 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d8082 q = 1) : d8082 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d8091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4907 q selected
    | true =>
      simp only [d8091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h4 (q : Pattern) (selected : d8092 q = 1) : d85633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8092, d85633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8092, d85633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8098 q = 1) : d8098 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d8099 q = 1) : d85634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8099, d85634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8099, d85634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8100 q = 1) : d85635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8100, d85635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8100, d85635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8101 q = 1) : d85636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8101, d85636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8101, d85636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8107 q = 1) : d8107 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d8111 q = 1) : d8111 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d8113 q = 1) : d8113 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d8115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4909 q selected
    | true =>
      simp only [d8115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h13 (q : Pattern) (selected : d8116 q = 1) : d85638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8116, d85638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d8116, d85638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8119 q = 1) : d8119 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d8120 q = 1) : d85639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8120, d85639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d8120, d85639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8121 q = 1) : d85640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8121, d85640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8121, d85640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d8122 q = 1) : d85641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8122, d85641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d8122, d85641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d8123 q = 1) : d85642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8123, d85642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8123, d85642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro4911 (p : Pattern) (selected : d8132 p = 1) : d85649 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8113 q = 1) : d8113 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d8115 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4909 q selected
    | true =>
      simp only [d8115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h3 (q : Pattern) (selected : d8116 q = 1) : d85638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8116, d85638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8116, d85638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8119 q = 1) : d8119 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d8120 q = 1) : d85639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8120, d85639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8120, d85639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8130 q = 1) : d85647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8130, d85647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8130, d85647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8131 q = 1) : d85648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8131, d85648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8131, d85648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8132 q = 1) : d85649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8132, d85649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8132, d85649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4912 (p : Pattern) (selected : d8156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2410 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro168 q selected
    | true =>
      simp only [d2410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro169 q selected
  have h2 (q : Pattern) (selected : d2411 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2412 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro169 q selected
    | true =>
      simp only [d2419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro170 q selected
  have h5 (q : Pattern) (selected : d2420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8155 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d8156 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d8156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro4913 (p : Pattern) (selected : d8162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8157 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4912 q selected
    | true =>
      simp only [d8157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8158 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2430 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro172 q selected
    | true =>
      simp only [d2430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8159 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8160 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d8161 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d8162 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4914 (p : Pattern) (selected : d8174 p = 1) : d85659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8154 q = 1) : d8154 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d8163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4913 q selected
    | true =>
      simp only [d8163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro174 q selected
  have h3 (q : Pattern) (selected : d8164 q = 1) : d85655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8164, d85655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8164, d85655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8170 q = 1) : d8170 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d8171 q = 1) : d85656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8171, d85656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8171, d85656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8172 q = 1) : d85657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8172, d85657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8172, d85657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8173 q = 1) : d85658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8173, d85658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8173, d85658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d8174 q = 1) : d85659 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8174, d85659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8174, d85659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4915 (p : Pattern) (selected : d8180 p = 1) : d85665 p = 1 := by
  have h0 (q : Pattern) (selected : d8061 q = 1) : d8061 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8124 q = 1) : d85643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8124, d85643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4908 q selected
    | true =>
      simp only [d8124, d85643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4910 q selected
  have h2 (q : Pattern) (selected : d8126 q = 1) : d8126 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d8127 q = 1) : d85644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8127, d85644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8127, d85644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d8128 q = 1) : d85645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8128, d85645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8128, d85645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8129 q = 1) : d85646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8129, d85646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8129, d85646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8133 q = 1) : d85650 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8133, d85650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8133, d85650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4911 q selected
  have h8 (q : Pattern) (selected : d2326 q = 1) : d2326 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d8134 q = 1) : d85651 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8134, d85651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d8134, d85651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8135 q = 1) : d85652 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8135, d85652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d8135, d85652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d8136 q = 1) : d85653 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8136, d85653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8136, d85653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d8137 q = 1) : d85654 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8137, d85654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8137, d85654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d8175 q = 1) : d85660 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8175, d85660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8175, d85660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4914 q selected
  have h14 (q : Pattern) (selected : d2459 q = 1) : d2459 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d8176 q = 1) : d85661 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8176, d85661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d8176, d85661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8177 q = 1) : d85662 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8177, d85662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d8177, d85662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d8178 q = 1) : d85663 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d8178, d85663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d8178, d85663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d8179 q = 1) : d85664 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d8179, d85664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d8179, d85664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d8180 q = 1) : d85665 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d8180, d85665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d8180, d85665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro4916 (p : Pattern) (selected : d8186 p = 1) : d85671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8181 q = 1) : d85666 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d8181, d85666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8181, d85666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4915 q selected
  have h2 (q : Pattern) (selected : d8182 q = 1) : d85667 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d8182, d85667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8182, d85667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d8183 q = 1) : d85668 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d8183, d85668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8183, d85668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d8184 q = 1) : d85669 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d8184, d85669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8184, d85669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d8185 q = 1) : d85670 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d8185, d85670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8185, d85670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d8186 q = 1) : d85671 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d8186, d85671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d8186, d85671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4917 (p : Pattern) (selected : d8192 p = 1) : d85677 p = 1 := by
  have h0 (q : Pattern) (selected : d7573 q = 1) : d85506 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d7573, d85506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4861 q selected
    | true =>
      simp only [d7573, d85506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4872 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d7725 q = 1) : d85546 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d7725, d85546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7725, d85546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4883 q selected
  have h3 (q : Pattern) (selected : d7726 q = 1) : d85547 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d7726, d85547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d7726, d85547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d7878 q = 1) : d85587 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d7878, d85587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7878, d85587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4894 q selected
  have h5 (q : Pattern) (selected : d7879 q = 1) : d85588 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d7879, d85588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d7879, d85588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d7880 q = 1) : d85589 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d7880, d85589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d7880, d85589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d8032 q = 1) : d85629 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d8032, d85629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8032, d85629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4905 q selected
  have h8 (q : Pattern) (selected : d8033 q = 1) : d85630 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d8033, d85630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8033, d85630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d8034 q = 1) : d85631 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d8034, d85631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8034, d85631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d8035 q = 1) : d85632 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d8035, d85632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d8035, d85632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d8187 q = 1) : d85672 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d8187, d85672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8187, d85672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4916 q selected
  have h12 (q : Pattern) (selected : d8188 q = 1) : d85673 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d8188, d85673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8188, d85673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d8189 q = 1) : d85674 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d8189, d85674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8189, d85674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d8190 q = 1) : d85675 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d8190, d85675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8190, d85675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d8191 q = 1) : d85676 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d8191, d85676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d8191, d85676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d8192 q = 1) : d85677 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d8192, d85677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d8192, d85677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro4918 (p : Pattern) (selected : d8198 p = 1) : d85683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8193 q = 1) : d85678 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d8193, d85678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4917 q selected
    | true =>
      simp only [d8193, d85678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8194 q = 1) : d85679 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d8194, d85679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8194, d85679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8195 q = 1) : d85680 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d8195, d85680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8195, d85680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8196 q = 1) : d85681 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d8196, d85681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8196, d85681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8197 q = 1) : d85682 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d8197, d85682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8197, d85682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8198 q = 1) : d85683 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d8198, d85683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8198, d85683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4919 (p : Pattern) (selected : d8204 p = 1) : d85689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8199 q = 1) : d85684 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d8199, d85684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4918 q selected
    | true =>
      simp only [d8199, d85684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8200 q = 1) : d85685 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d8200, d85685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8200, d85685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8201 q = 1) : d85686 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d8201, d85686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8201, d85686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8202 q = 1) : d85687 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d8202, d85687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8202, d85687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8203 q = 1) : d85688 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d8203, d85688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8203, d85688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8204 q = 1) : d85689 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d8204, d85689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8204, d85689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4920 (p : Pattern) (selected : d8210 p = 1) : d85695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8205 q = 1) : d85690 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d8205, d85690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4919 q selected
    | true =>
      simp only [d8205, d85690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8206 q = 1) : d85691 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d8206, d85691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8206, d85691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8207 q = 1) : d85692 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d8207, d85692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8207, d85692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8208 q = 1) : d85693 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d8208, d85693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8208, d85693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8209 q = 1) : d85694 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d8209, d85694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8209, d85694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8210 q = 1) : d85695 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d8210, d85695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8210, d85695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4921 (p : Pattern) (selected : d8216 p = 1) : d85701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8211 q = 1) : d85696 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d8211, d85696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4920 q selected
    | true =>
      simp only [d8211, d85696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8212 q = 1) : d85697 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d8212, d85697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8212, d85697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8213 q = 1) : d85698 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d8213, d85698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8213, d85698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8214 q = 1) : d85699 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d8214, d85699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8214, d85699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8215 q = 1) : d85700 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d8215, d85700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8215, d85700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8216 q = 1) : d85701 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d8216, d85701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8216, d85701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4922 (p : Pattern) (selected : d8222 p = 1) : d85707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8217 q = 1) : d85702 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d8217, d85702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4921 q selected
    | true =>
      simp only [d8217, d85702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8218 q = 1) : d85703 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d8218, d85703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8218, d85703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8219 q = 1) : d85704 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d8219, d85704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8219, d85704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8220 q = 1) : d85705 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d8220, d85705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8220, d85705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8221 q = 1) : d85706 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d8221, d85706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8221, d85706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8222 q = 1) : d85707 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d8222, d85707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8222, d85707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4923 (p : Pattern) (selected : d8228 p = 1) : d85713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8223 q = 1) : d85708 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d8223, d85708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4922 q selected
    | true =>
      simp only [d8223, d85708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8224 q = 1) : d85709 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d8224, d85709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8224, d85709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8225 q = 1) : d85710 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d8225, d85710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8225, d85710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8226 q = 1) : d85711 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d8226, d85711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8226, d85711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8227 q = 1) : d85712 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d8227, d85712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8227, d85712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8228 q = 1) : d85713 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d8228, d85713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8228, d85713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4924 (p : Pattern) (selected : d8234 p = 1) : d85719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d8229 q = 1) : d85714 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d8229, d85714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4923 q selected
    | true =>
      simp only [d8229, d85714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d8230 q = 1) : d85715 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d8230, d85715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d8230, d85715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d8231 q = 1) : d85716 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d8231, d85716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d8231, d85716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d8232 q = 1) : d85717 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d8232, d85717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d8232, d85717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d8233 q = 1) : d85718 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d8233, d85718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d8233, d85718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d8234 q = 1) : d85719 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d8234, d85719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d8234, d85719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4925 (p : Pattern) (selected : d85728 p = 0) : d87047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85725 q = 0) : d87044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85725, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85725, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h2 (q : Pattern) (selected : d85726 q = 0) : d87045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85726, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85726, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85727 q = 0) : d87046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85727, d87046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85727, d87046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85728 q = 0) : d87047 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85728, d87047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85728, d87047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro4926 (p : Pattern) (selected : d85734 p = 0) : d87053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85731 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85732 q = 0) : d87051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85733 q = 0) : d87052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85733, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85733, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85734 q = 0) : d87053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85734, d87053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85734, d87053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4927 (p : Pattern) (selected : d85740 p = 0) : d87059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85736 q = 0) : d87055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85737 q = 0) : d87056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85737, d87056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85737, d87056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85738 q = 0) : d87057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85738, d87057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85738, d87057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85739 q = 0) : d87058 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85739, d87058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85739, d87058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85740 q = 0) : d87059 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85740, d87059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85740, d87059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4928 (p : Pattern) (selected : d85741 p = 0) : d87060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85731 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85732 q = 0) : d87051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85733 q = 0) : d87052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85733, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85733, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85741 q = 0) : d87060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85741, d87060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85741, d87060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4929 (p : Pattern) (selected : d85747 p = 0) : d87066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85736 q = 0) : d87055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85737 q = 0) : d87056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85737, d87056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85737, d87056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85738 q = 0) : d87057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85738, d87057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85738, d87057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85739 q = 0) : d87058 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85739, d87058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85739, d87058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85742 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
    | true =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85743 q = 0) : d87062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85744 q = 0) : d87063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85744, d87063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85744, d87063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d85745 q = 0) : d87064 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85745, d87064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85745, d87064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85746 q = 0) : d87065 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85746, d87065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85746, d87065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85747 q = 0) : d87066 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85747, d87066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85747, d87066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4930 (p : Pattern) (selected : d85752 p = 0) : d87071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85742 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
    | true =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85743 q = 0) : d87062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85744 q = 0) : d87063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85744, d87063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85744, d87063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85745 q = 0) : d87064 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85745, d87064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85745, d87064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85746 q = 0) : d87065 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85746, d87065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85746, d87065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85752 q = 0) : d87071 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85752, d87071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85752, d87071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4931 (p : Pattern) (selected : d85761 p = 0) : d87080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85758 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h2 (q : Pattern) (selected : d85759 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85760 q = 0) : d87079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85760, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85760, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85761 q = 0) : d87080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85761, d87080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85761, d87080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro4932 (p : Pattern) (selected : d85767 p = 0) : d87086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85762 q = 0) : d87081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85762, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4931 q selected
    | true =>
      simp only [d85762, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85763 q = 0) : d87082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85763, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85763, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85764 q = 0) : d87083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85764, d87083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85764, d87083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85765 q = 0) : d87084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85765, d87084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85765, d87084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85766 q = 0) : d87085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85766, d87085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85766, d87085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85767 q = 0) : d87086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85767, d87086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85767, d87086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4933 (p : Pattern) (selected : d85773 p = 0) : d87092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85768 q = 0) : d87087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85768, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4932 q selected
    | true =>
      simp only [d85768, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85769 q = 0) : d87088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85769, d87088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85769, d87088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85770 q = 0) : d87089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85770, d87089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85770, d87089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85771 q = 0) : d87090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85771, d87090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85771, d87090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85772 q = 0) : d87091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85772, d87091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85772, d87091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85773 q = 0) : d87092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85773, d87092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85773, d87092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4934 (p : Pattern) (selected : d85779 p = 0) : d87098 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85748 q = 0) : d87067 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85748, d87067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4927 q selected
    | true =>
      simp only [d85748, d87067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4929 q selected
  have h2 (q : Pattern) (selected : d85749 q = 0) : d87068 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85749, d87068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85749, d87068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85750 q = 0) : d87069 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85750, d87069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85750, d87069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85751 q = 0) : d87070 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85751, d87070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85751, d87070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85753 q = 0) : d87072 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85753, d87072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85753, d87072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4930 q selected
  have h6 (q : Pattern) (selected : d85754 q = 0) : d87073 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85754, d87073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85754, d87073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85755 q = 0) : d87074 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85755, d87074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85755, d87074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85756 q = 0) : d87075 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85756, d87075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85756, d87075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d85757 q = 0) : d87076 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85757, d87076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85757, d87076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85774 q = 0) : d87093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85774, d87093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85774, d87093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4933 q selected
  have h11 (q : Pattern) (selected : d85775 q = 0) : d87094 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85775, d87094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85775, d87094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d85776 q = 0) : d87095 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85776, d87095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85776, d87095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d85777 q = 0) : d87096 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85777, d87096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d85777, d87096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d85778 q = 0) : d87097 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85778, d87097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d85778, d87097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d85779 q = 0) : d87098 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85779, d87098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d85779, d87098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro4935 (p : Pattern) (selected : d85789 p = 0) : d87108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85785 q = 0) : d87104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85786 q = 0) : d87105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85787 q = 0) : d87106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85788 q = 0) : d87107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85789 q = 0) : d87108 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85789, d87108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85789, d87108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4936 (p : Pattern) (selected : d85796 p = 0) : d87115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85785 q = 0) : d87104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85786 q = 0) : d87105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85787 q = 0) : d87106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85788 q = 0) : d87107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85742 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
    | true =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85792 q = 0) : d87111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85792, d87111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85792, d87111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85793 q = 0) : d87112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85793, d87112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85793, d87112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d85794 q = 0) : d87113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85794, d87113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85794, d87113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85795 q = 0) : d87114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85795, d87114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85795, d87114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85796 q = 0) : d87115 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85796, d87115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85796, d87115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4937 (p : Pattern) (selected : d85801 p = 0) : d87120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85731 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85732 q = 0) : d87051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85800 q = 0) : d87119 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85800, d87119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85800, d87119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85801 q = 0) : d87120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85801, d87120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85801, d87120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4938 (p : Pattern) (selected : d85808 p = 0) : d87127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85731 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85806 q = 0) : d87125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85806, d87125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85806, d87125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85807 q = 0) : d87126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85807, d87126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85807, d87126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85808 q = 0) : d87127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85808, d87127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85808, d87127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4939 (p : Pattern) (selected : d85815 p = 0) : d87134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85812 q = 0) : d87131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85812, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85812, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
  have h2 (q : Pattern) (selected : d85813 q = 0) : d87132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85813, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85813, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85725 q = 0) : d87044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85725, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85725, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h4 (q : Pattern) (selected : d85726 q = 0) : d87045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85726, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85726, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85814 q = 0) : d87133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85814, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85814, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85815 q = 0) : d87134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85815, d87134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85815, d87134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4940 (p : Pattern) (selected : d85821 p = 0) : d87140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85818 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85819 q = 0) : d87138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85820 q = 0) : d87139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85820, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85820, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85821 q = 0) : d87140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85821, d87140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85821, d87140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4941 (p : Pattern) (selected : d85826 p = 0) : d87047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85823 q = 0) : d87044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85823, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85823, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h2 (q : Pattern) (selected : d85824 q = 0) : d87045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85824, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85824, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85825 q = 0) : d87046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85825, d87046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85825, d87046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85826 q = 0) : d87047 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85826, d87047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85826, d87047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro4942 (p : Pattern) (selected : d85832 p = 0) : d87053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85827 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4941 q selected
    | true =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85828 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85829 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85829, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85829, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85830 q = 0) : d87051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85830, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85830, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85831 q = 0) : d87052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85831, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85831, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85832 q = 0) : d87053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85832, d87053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85832, d87053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4943 (p : Pattern) (selected : d85838 p = 0) : d87146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85802 q = 0) : d87121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85802, d87121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4937 q selected
    | true =>
      simp only [d85802, d87121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85803 q = 0) : d87122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85803, d87122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85803, d87122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85804 q = 0) : d87123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85804, d87123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85804, d87123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85805 q = 0) : d87124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85805, d87124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85805, d87124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85809 q = 0) : d87128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85809, d87128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4938 q selected
    | true =>
      simp only [d85809, d87128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85810 q = 0) : d87129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85810, d87129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85810, d87129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85811 q = 0) : d87130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85811, d87130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85811, d87130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85822 q = 0) : d87141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4940 q selected
    | true =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
  have h9 (q : Pattern) (selected : d85833 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85833, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4942 q selected
    | true =>
      simp only [d85833, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d85834 q = 0) : d87142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85834, d87142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85834, d87142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d85736 q = 0) : d87055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d85835 q = 0) : d87143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85835, d87143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85835, d87143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d85836 q = 0) : d87144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85836, d87144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85836, d87144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d85837 q = 0) : d87145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85837, d87145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85837, d87145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d85838 q = 0) : d87146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85838, d87146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85838, d87146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4944 (p : Pattern) (selected : d85839 p = 0) : d87147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85731 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85732 q = 0) : d87051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85732, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85800 q = 0) : d87119 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85800, d87119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85800, d87119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85839 q = 0) : d87147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85839, d87147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85839, d87147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4945 (p : Pattern) (selected : d85844 p = 0) : d87152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85731 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85731, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85806 q = 0) : d87125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85806, d87125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85806, d87125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85807 q = 0) : d87126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85807, d87126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85807, d87126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85844 q = 0) : d87152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85844, d87152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85844, d87152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4946 (p : Pattern) (selected : d85848 p = 0) : d87156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85818 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85819 q = 0) : d87138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85820 q = 0) : d87139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85820, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85820, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85848 q = 0) : d87156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85848, d87156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85848, d87156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4947 (p : Pattern) (selected : d85850 p = 0) : d87060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85827 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4941 q selected
    | true =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85828 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85829 q = 0) : d87050 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85829, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85829, d87050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85830 q = 0) : d87051 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85830, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85830, d87051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85831 q = 0) : d87052 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85831, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85831, d87052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85850 q = 0) : d87060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85850, d87060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85850, d87060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4948 (p : Pattern) (selected : d85856 p = 0) : d87162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85802 q = 0) : d87121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85802, d87121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4937 q selected
    | true =>
      simp only [d85802, d87121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85803 q = 0) : d87122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85803, d87122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85803, d87122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85804 q = 0) : d87123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85804, d87123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85804, d87123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85805 q = 0) : d87124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85805, d87124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85805, d87124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85809 q = 0) : d87128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85809, d87128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4938 q selected
    | true =>
      simp only [d85809, d87128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85810 q = 0) : d87129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85810, d87129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85810, d87129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85811 q = 0) : d87130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85811, d87130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85811, d87130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85822 q = 0) : d87141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4940 q selected
    | true =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
  have h9 (q : Pattern) (selected : d85833 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85833, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4942 q selected
    | true =>
      simp only [d85833, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d85834 q = 0) : d87142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85834, d87142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85834, d87142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d85736 q = 0) : d87055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85736, d87055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d85835 q = 0) : d87143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85835, d87143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85835, d87143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d85836 q = 0) : d87144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85836, d87144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85836, d87144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d85837 q = 0) : d87145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85837, d87145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85837, d87145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d85840 q = 0) : d87148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85840, d87148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4944 q selected
    | true =>
      simp only [d85840, d87148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d85841 q = 0) : d87149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85841, d87149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85841, d87149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d85842 q = 0) : d87150 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85842, d87150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d85842, d87150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d85843 q = 0) : d87151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85843, d87151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85843, d87151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d85845 q = 0) : d87153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85845, d87153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4945 q selected
    | true =>
      simp only [d85845, d87153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d85846 q = 0) : d87154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85846, d87154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85846, d87154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d85847 q = 0) : d87155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85847, d87155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d85847, d87155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d85849 q = 0) : d87157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85849, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4946 q selected
    | true =>
      simp only [d85849, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
  have h24 (q : Pattern) (selected : d85851 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85851, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4947 q selected
    | true =>
      simp only [d85851, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d85852 q = 0) : d87158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85852, d87158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d85852, d87158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d85742 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
    | true =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d85743 q = 0) : d87062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d85853 q = 0) : d87159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85853, d87159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d85853, d87159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d85854 q = 0) : d87160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85854, d87160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d85854, d87160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d85855 q = 0) : d87161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85855, d87161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d85855, d87161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d85856 q = 0) : d87162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85856, d87162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d85856, d87162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4949 (p : Pattern) (selected : d85858 p = 0) : d87164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85785 q = 0) : d87104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85786 q = 0) : d87105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85787 q = 0) : d87106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85788 q = 0) : d87107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85858 q = 0) : d87164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85858, d87164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85858, d87164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4950 (p : Pattern) (selected : d85865 p = 0) : d87171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85849 q = 0) : d87157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85849, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4946 q selected
    | true =>
      simp only [d85849, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
  have h2 (q : Pattern) (selected : d85851 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85851, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4947 q selected
    | true =>
      simp only [d85851, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85852 q = 0) : d87158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85852, d87158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85852, d87158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85742 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
    | true =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85743 q = 0) : d87062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85743, d87062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85853 q = 0) : d87159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85853, d87159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85853, d87159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85863 q = 0) : d87169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85863, d87169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85863, d87169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85864 q = 0) : d87170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85864, d87170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85864, d87170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85865 q = 0) : d87171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85865, d87171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85865, d87171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4951 (p : Pattern) (selected : d85874 p = 0) : d87180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85871 q = 0) : d87177 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h2 (q : Pattern) (selected : d85872 q = 0) : d87178 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85758 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h4 (q : Pattern) (selected : d85759 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85873 q = 0) : d87179 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85873, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85873, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85874 q = 0) : d87180 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85874, d87180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85874, d87180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4952 (p : Pattern) (selected : d85880 p = 0) : d87186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85875 q = 0) : d87181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85875, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4951 q selected
    | true =>
      simp only [d85875, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85876 q = 0) : d87182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85876, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85876, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85762 q = 0) : d87081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85762, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4931 q selected
    | true =>
      simp only [d85762, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85763 q = 0) : d87082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85763, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85763, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85877 q = 0) : d87183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85877, d87183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85877, d87183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85878 q = 0) : d87184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85878, d87184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85878, d87184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85879 q = 0) : d87185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85879, d87185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85879, d87185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85880 q = 0) : d87186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85880, d87186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85880, d87186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4953 (p : Pattern) (selected : d85885 p = 0) : d87080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85882 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h2 (q : Pattern) (selected : d85883 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85884 q = 0) : d87079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85884, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85884, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85885 q = 0) : d87080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85885, d87080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85885, d87080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro4954 (p : Pattern) (selected : d85891 p = 0) : d87086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85886 q = 0) : d87081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85886, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4953 q selected
    | true =>
      simp only [d85886, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85887 q = 0) : d87082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85887, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85887, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85888 q = 0) : d87083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85888, d87083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85888, d87083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85889 q = 0) : d87084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85889, d87084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85889, d87084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85890 q = 0) : d87085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85890, d87085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85890, d87085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85891 q = 0) : d87086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85891, d87086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85891, d87086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4955 (p : Pattern) (selected : d85897 p = 0) : d87192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85881 q = 0) : d87187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85881, d87187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4952 q selected
    | true =>
      simp only [d85881, d87187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4932 q selected
  have h2 (q : Pattern) (selected : d85892 q = 0) : d87087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85892, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4954 q selected
    | true =>
      simp only [d85892, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85893 q = 0) : d87188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85893, d87188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85893, d87188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85768 q = 0) : d87087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85768, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4932 q selected
    | true =>
      simp only [d85768, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85769 q = 0) : d87088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85769, d87088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85769, d87088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85894 q = 0) : d87189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85894, d87189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85894, d87189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85895 q = 0) : d87190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85895, d87190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85895, d87190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85896 q = 0) : d87191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85896, d87191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85896, d87191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85897 q = 0) : d87192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85897, d87192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85897, d87192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4956 (p : Pattern) (selected : d85903 p = 0) : d87198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85790 q = 0) : d87109 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85790, d87109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85790, d87109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4935 q selected
  have h2 (q : Pattern) (selected : d85791 q = 0) : d87110 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85791, d87110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85791, d87110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85797 q = 0) : d87116 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85797, d87116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4935 q selected
    | true =>
      simp only [d85797, d87116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4936 q selected
  have h4 (q : Pattern) (selected : d85798 q = 0) : d87117 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85798, d87117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85798, d87117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85799 q = 0) : d87118 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85799, d87118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85799, d87118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85857 q = 0) : d87163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85857, d87163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4943 q selected
    | true =>
      simp only [d85857, d87163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4948 q selected
  have h7 (q : Pattern) (selected : d85859 q = 0) : d87165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85859, d87165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4949 q selected
    | true =>
      simp only [d85859, d87165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85860 q = 0) : d87166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85860, d87166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85860, d87166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85861 q = 0) : d87167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85861, d87167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85861, d87167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d85862 q = 0) : d87168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85862, d87168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85862, d87168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85866 q = 0) : d87172 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85866, d87172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85866, d87172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4950 q selected
  have h12 (q : Pattern) (selected : d85867 q = 0) : d87173 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85867, d87173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85867, d87173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d85868 q = 0) : d87174 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85868, d87174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d85868, d87174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d85869 q = 0) : d87175 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85869, d87175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d85869, d87175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d85870 q = 0) : d87176 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85870, d87176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85870, d87176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d85898 q = 0) : d87193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85898, d87193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85898, d87193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4955 q selected
  have h17 (q : Pattern) (selected : d85899 q = 0) : d87194 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85899, d87194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d85899, d87194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d85900 q = 0) : d87195 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85900, d87195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d85900, d87195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d85901 q = 0) : d87196 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85901, d87196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d85901, d87196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d85902 q = 0) : d87197 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85902, d87197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d85902, d87197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d85903 q = 0) : d87198 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85903, d87198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d85903, d87198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro4957 (p : Pattern) (selected : d85909 p = 0) : d87204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85780 q = 0) : d87099 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85780, d87099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85780, d87099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4934 q selected
  have h2 (q : Pattern) (selected : d85781 q = 0) : d87100 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85781, d87100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85781, d87100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85782 q = 0) : d87101 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85782, d87101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85782, d87101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85783 q = 0) : d87102 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85783, d87102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85783, d87102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85784 q = 0) : d87103 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85784, d87103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85784, d87103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85904 q = 0) : d87199 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85904, d87199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85904, d87199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4956 q selected
  have h7 (q : Pattern) (selected : d85905 q = 0) : d87200 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85905, d87200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85905, d87200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85906 q = 0) : d87201 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85906, d87201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85906, d87201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85907 q = 0) : d87202 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85907, d87202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85907, d87202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85908 q = 0) : d87203 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85908, d87203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85908, d87203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85909 q = 0) : d87204 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85909, d87204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85909, d87204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4958 (p : Pattern) (selected : d85914 p = 0) : d87209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85822 q = 0) : d87141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4940 q selected
    | true =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
  have h2 (q : Pattern) (selected : d85910 q = 0) : d87205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85910, d87205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85910, d87205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85911 q = 0) : d87206 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85911, d87206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85911, d87206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85912 q = 0) : d87207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85912, d87207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85912, d87207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85913 q = 0) : d87208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85913, d87208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85913, d87208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85914 q = 0) : d87209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85914, d87209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85914, d87209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4959 (p : Pattern) (selected : d85921 p = 0) : d87216 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85822 q = 0) : d87141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4940 q selected
    | true =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
  have h2 (q : Pattern) (selected : d85910 q = 0) : d87205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85910, d87205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85910, d87205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85911 q = 0) : d87206 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85911, d87206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85911, d87206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85912 q = 0) : d87207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85912, d87207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85912, d87207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85913 q = 0) : d87208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85913, d87208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85913, d87208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85849 q = 0) : d87157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85849, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4946 q selected
    | true =>
      simp only [d85849, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
  have h7 (q : Pattern) (selected : d85917 q = 0) : d87212 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85917, d87212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85917, d87212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85918 q = 0) : d87213 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85918, d87213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85918, d87213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d85919 q = 0) : d87214 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85919, d87214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85919, d87214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85920 q = 0) : d87215 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85920, d87215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85920, d87215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85921 q = 0) : d87216 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85921, d87216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85921, d87216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4960 (p : Pattern) (selected : d85926 p = 0) : d87221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85818 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85819 q = 0) : d87138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85925 q = 0) : d87220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85925, d87220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85925, d87220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85926 q = 0) : d87221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85926, d87221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85926, d87221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4961 (p : Pattern) (selected : d85933 p = 0) : d87228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85818 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85931 q = 0) : d87226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85931, d87226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85931, d87226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85932 q = 0) : d87227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85932, d87227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85932, d87227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85933 q = 0) : d87228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85933, d87228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85933, d87228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4962 (p : Pattern) (selected : d85940 p = 0) : d87235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85937 q = 0) : d87232 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85937, d87232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85937, d87232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
  have h2 (q : Pattern) (selected : d85938 q = 0) : d87233 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85938, d87233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85938, d87233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85812 q = 0) : d87131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85812, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85812, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
  have h4 (q : Pattern) (selected : d85813 q = 0) : d87132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85813, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85813, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85939 q = 0) : d87234 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85939, d87234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85939, d87234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85940 q = 0) : d87235 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85940, d87235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85940, d87235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4963 (p : Pattern) (selected : d85946 p = 0) : d87241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85941 q = 0) : d87236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85941, d87236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4962 q selected
    | true =>
      simp only [d85941, d87236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85942 q = 0) : d87237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85942, d87237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85942, d87237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85943 q = 0) : d87238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85943, d87238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85943, d87238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85944 q = 0) : d87239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85944, d87239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85944, d87239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85945 q = 0) : d87240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85945, d87240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85945, d87240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85946 q = 0) : d87241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85946, d87241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85946, d87241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4964 (p : Pattern) (selected : d85951 p = 0) : d87134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85948 q = 0) : d87131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85948, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85948, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
  have h2 (q : Pattern) (selected : d85949 q = 0) : d87132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85949, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85949, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85823 q = 0) : d87044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85823, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85823, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h4 (q : Pattern) (selected : d85824 q = 0) : d87045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85824, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85824, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85950 q = 0) : d87133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85950, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85950, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85951 q = 0) : d87134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d85951, d87134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85951, d87134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4965 (p : Pattern) (selected : d85957 p = 0) : d87140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85952 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85952, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4964 q selected
    | true =>
      simp only [d85952, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85953 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85953, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85953, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85827 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4941 q selected
    | true =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85828 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85954 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85954, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85954, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85955 q = 0) : d87138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85955, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85955, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85956 q = 0) : d87139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85956, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85956, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85957 q = 0) : d87140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85957, d87140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85957, d87140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4966 (p : Pattern) (selected : d85963 p = 0) : d87247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85960 q = 0) : d87244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85960, d87244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85960, d87244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85961 q = 0) : d87245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85961, d87245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85961, d87245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85962 q = 0) : d87246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85962, d87246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85962, d87246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85963 q = 0) : d87247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85963, d87247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85963, d87247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4967 (p : Pattern) (selected : d85969 p = 0) : d87253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85927 q = 0) : d87222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85927, d87222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4960 q selected
    | true =>
      simp only [d85927, d87222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4937 q selected
  have h2 (q : Pattern) (selected : d85928 q = 0) : d87223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85928, d87223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85928, d87223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85929 q = 0) : d87224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85929, d87224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85929, d87224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85930 q = 0) : d87225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85930, d87225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85930, d87225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85934 q = 0) : d87229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85934, d87229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4961 q selected
    | true =>
      simp only [d85934, d87229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4938 q selected
  have h6 (q : Pattern) (selected : d85935 q = 0) : d87230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85935, d87230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85935, d87230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85936 q = 0) : d87231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85936, d87231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85936, d87231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85947 q = 0) : d87242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85947, d87242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4963 q selected
    | true =>
      simp only [d85947, d87242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4940 q selected
  have h9 (q : Pattern) (selected : d85958 q = 0) : d87141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85958, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4965 q selected
    | true =>
      simp only [d85958, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4942 q selected
  have h10 (q : Pattern) (selected : d85959 q = 0) : d87243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85959, d87243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85959, d87243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85964 q = 0) : d87248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85964, d87248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4966 q selected
    | true =>
      simp only [d85964, d87248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d85965 q = 0) : d87249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85965, d87249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85965, d87249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d85966 q = 0) : d87250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85966, d87250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85966, d87250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d85967 q = 0) : d87251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85967, d87251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85967, d87251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d85968 q = 0) : d87252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85968, d87252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85968, d87252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d85969 q = 0) : d87253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85969, d87253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85969, d87253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro4968 (p : Pattern) (selected : d85970 p = 0) : d87254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85818 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85819 q = 0) : d87138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85819, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85925 q = 0) : d87220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85925, d87220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85925, d87220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85970 q = 0) : d87254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85970, d87254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85970, d87254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4969 (p : Pattern) (selected : d85975 p = 0) : d87259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85729 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4925 q selected
    | true =>
      simp only [d85729, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85730 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85730, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85818 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85818, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85931 q = 0) : d87226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85931, d87226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85931, d87226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85932 q = 0) : d87227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85932, d87227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85932, d87227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85975 q = 0) : d87259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85975, d87259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85975, d87259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4970 (p : Pattern) (selected : d85979 p = 0) : d87263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85941 q = 0) : d87236 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85941, d87236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4962 q selected
    | true =>
      simp only [d85941, d87236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85942 q = 0) : d87237 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85942, d87237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85942, d87237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85943 q = 0) : d87238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85943, d87238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85943, d87238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85944 q = 0) : d87239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85944, d87239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85944, d87239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85945 q = 0) : d87240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85945, d87240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85945, d87240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85979 q = 0) : d87263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85979, d87263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85979, d87263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4971 (p : Pattern) (selected : d85981 p = 0) : d87156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85952 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85952, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4964 q selected
    | true =>
      simp only [d85952, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85953 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85953, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85953, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85827 q = 0) : d87048 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4941 q selected
    | true =>
      simp only [d85827, d87048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85828 q = 0) : d87049 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85828, d87049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85954 q = 0) : d87137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85954, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85954, d87137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85955 q = 0) : d87138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85955, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85955, d87138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85956 q = 0) : d87139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85956, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85956, d87139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85981 q = 0) : d87156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85981, d87156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85981, d87156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4972 (p : Pattern) (selected : d85984 p = 0) : d87266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85816 q = 0) : d87135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4939 q selected
    | true =>
      simp only [d85816, d87135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85817 q = 0) : d87136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85817, d87136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85960 q = 0) : d87244 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d85960, d87244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85960, d87244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85961 q = 0) : d87245 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d85961, d87245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85961, d87245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85962 q = 0) : d87246 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d85962, d87246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85962, d87246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85984 q = 0) : d87266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d85984, d87266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85984, d87266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4973 (p : Pattern) (selected : d85990 p = 0) : d87272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85927 q = 0) : d87222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85927, d87222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4960 q selected
    | true =>
      simp only [d85927, d87222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4937 q selected
  have h2 (q : Pattern) (selected : d85928 q = 0) : d87223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85928, d87223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85928, d87223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85929 q = 0) : d87224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85929, d87224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85929, d87224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85930 q = 0) : d87225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85930, d87225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85930, d87225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85934 q = 0) : d87229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85934, d87229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4961 q selected
    | true =>
      simp only [d85934, d87229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4938 q selected
  have h6 (q : Pattern) (selected : d85935 q = 0) : d87230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85935, d87230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85935, d87230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85936 q = 0) : d87231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85936, d87231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85936, d87231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d85947 q = 0) : d87242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85947, d87242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4963 q selected
    | true =>
      simp only [d85947, d87242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4940 q selected
  have h9 (q : Pattern) (selected : d85958 q = 0) : d87141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85958, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4965 q selected
    | true =>
      simp only [d85958, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4942 q selected
  have h10 (q : Pattern) (selected : d85959 q = 0) : d87243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85959, d87243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85959, d87243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85964 q = 0) : d87248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85964, d87248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4966 q selected
    | true =>
      simp only [d85964, d87248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d85965 q = 0) : d87249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85965, d87249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d85965, d87249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d85966 q = 0) : d87250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85966, d87250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d85966, d87250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d85967 q = 0) : d87251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85967, d87251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85967, d87251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d85968 q = 0) : d87252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85968, d87252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85968, d87252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d85971 q = 0) : d87255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85971, d87255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4968 q selected
    | true =>
      simp only [d85971, d87255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4944 q selected
  have h17 (q : Pattern) (selected : d85972 q = 0) : d87256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85972, d87256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85972, d87256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d85973 q = 0) : d87257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85973, d87257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d85973, d87257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d85974 q = 0) : d87258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85974, d87258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85974, d87258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d85976 q = 0) : d87260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85976, d87260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4969 q selected
    | true =>
      simp only [d85976, d87260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4945 q selected
  have h21 (q : Pattern) (selected : d85977 q = 0) : d87261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85977, d87261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85977, d87261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d85978 q = 0) : d87262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85978, d87262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d85978, d87262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d85980 q = 0) : d87264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85980, d87264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4970 q selected
    | true =>
      simp only [d85980, d87264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4946 q selected
  have h24 (q : Pattern) (selected : d85982 q = 0) : d87157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85982, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4971 q selected
    | true =>
      simp only [d85982, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4947 q selected
  have h25 (q : Pattern) (selected : d85983 q = 0) : d87265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85983, d87265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d85983, d87265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d85985 q = 0) : d87267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85985, d87267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4972 q selected
    | true =>
      simp only [d85985, d87267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d85986 q = 0) : d87268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85986, d87268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d85986, d87268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d85987 q = 0) : d87269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85987, d87269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d85987, d87269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d85988 q = 0) : d87270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85988, d87270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d85988, d87270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d85989 q = 0) : d87271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85989, d87271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d85989, d87271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d85990 q = 0) : d87272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85990, d87272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d85990, d87272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro4974 (p : Pattern) (selected : d85992 p = 0) : d87274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85822 q = 0) : d87141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4940 q selected
    | true =>
      simp only [d85822, d87141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
  have h2 (q : Pattern) (selected : d85910 q = 0) : d87205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85910, d87205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85910, d87205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85911 q = 0) : d87206 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85911, d87206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85911, d87206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85912 q = 0) : d87207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85912, d87207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85912, d87207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85913 q = 0) : d87208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85913, d87208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85913, d87208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85735 q = 0) : d87054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4926 q selected
    | true =>
      simp only [d85735, d87054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d85785 q = 0) : d87104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85785, d87104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85786 q = 0) : d87105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d85786, d87105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d85787 q = 0) : d87106 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85787, d87106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d85788 q = 0) : d87107 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85788, d87107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d85992 q = 0) : d87274 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85992, d87274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85992, d87274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4975 (p : Pattern) (selected : d85999 p = 0) : d87281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85980 q = 0) : d87264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85980, d87264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4970 q selected
    | true =>
      simp only [d85980, d87264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4946 q selected
  have h2 (q : Pattern) (selected : d85982 q = 0) : d87157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85982, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4971 q selected
    | true =>
      simp only [d85982, d87157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4947 q selected
  have h3 (q : Pattern) (selected : d85983 q = 0) : d87265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85983, d87265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85983, d87265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85985 q = 0) : d87267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85985, d87267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4972 q selected
    | true =>
      simp only [d85985, d87267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85986 q = 0) : d87268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85986, d87268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85986, d87268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d85987 q = 0) : d87269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85987, d87269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85987, d87269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d85997 q = 0) : d87279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85997, d87279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85997, d87279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85998 q = 0) : d87280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85998, d87280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85998, d87280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85999 q = 0) : d87281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85999, d87281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85999, d87281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4976 (p : Pattern) (selected : d86001 p = 0) : d87283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85742 q = 0) : d87061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4928 q selected
    | true =>
      simp only [d85742, d87061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85792 q = 0) : d87111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85792, d87111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85792, d87111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85793 q = 0) : d87112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85793, d87112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85793, d87112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85794 q = 0) : d87113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85794, d87113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85794, d87113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85795 q = 0) : d87114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85795, d87114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85795, d87114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86001 q = 0) : d87283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86001, d87283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86001, d87283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4977 (p : Pattern) (selected : d86010 p = 0) : d87292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86007 q = 0) : d87289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86007, d87289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86007, d87289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
  have h2 (q : Pattern) (selected : d86008 q = 0) : d87290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86008, d87290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86008, d87290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85871 q = 0) : d87177 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h4 (q : Pattern) (selected : d85872 q = 0) : d87178 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86009 q = 0) : d87291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86009, d87291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86009, d87291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86010 q = 0) : d87292 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86010, d87292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86010, d87292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4978 (p : Pattern) (selected : d86016 p = 0) : d87298 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86011 q = 0) : d87293 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86011, d87293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4977 q selected
    | true =>
      simp only [d86011, d87293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86012 q = 0) : d87294 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86012, d87294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86012, d87294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85875 q = 0) : d87181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85875, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4951 q selected
    | true =>
      simp only [d85875, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85876 q = 0) : d87182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85876, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85876, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86013 q = 0) : d87295 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86013, d87295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86013, d87295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86014 q = 0) : d87296 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86014, d87296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86014, d87296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86015 q = 0) : d87297 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86015, d87297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86015, d87297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86016 q = 0) : d87298 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86016, d87298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86016, d87298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4979 (p : Pattern) (selected : d86021 p = 0) : d87180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86018 q = 0) : d87177 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86018, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86018, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
  have h2 (q : Pattern) (selected : d86019 q = 0) : d87178 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86019, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86019, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85882 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h4 (q : Pattern) (selected : d85883 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86020 q = 0) : d87179 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86020, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86020, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86021 q = 0) : d87180 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86021, d87180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86021, d87180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4980 (p : Pattern) (selected : d86027 p = 0) : d87186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86022 q = 0) : d87181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86022, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4979 q selected
    | true =>
      simp only [d86022, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86023 q = 0) : d87182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86023, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86023, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85886 q = 0) : d87081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85886, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4953 q selected
    | true =>
      simp only [d85886, d87081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d85887 q = 0) : d87082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85887, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85887, d87082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86024 q = 0) : d87183 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86024, d87183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86024, d87183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86025 q = 0) : d87184 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86025, d87184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86025, d87184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86026 q = 0) : d87185 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86026, d87185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86026, d87185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86027 q = 0) : d87186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86027, d87186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86027, d87186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4981 (p : Pattern) (selected : d86033 p = 0) : d87304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85875 q = 0) : d87181 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d85875, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4951 q selected
    | true =>
      simp only [d85875, d87181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d85876 q = 0) : d87182 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d85876, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85876, d87182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86030 q = 0) : d87301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86030, d87301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86030, d87301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86031 q = 0) : d87302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86031, d87302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86031, d87302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86032 q = 0) : d87303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86032, d87303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86032, d87303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86033 q = 0) : d87304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86033, d87304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86033, d87304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4982 (p : Pattern) (selected : d86039 p = 0) : d87310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86017 q = 0) : d87299 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86017, d87299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4978 q selected
    | true =>
      simp only [d86017, d87299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4952 q selected
  have h2 (q : Pattern) (selected : d86028 q = 0) : d87187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86028, d87187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4980 q selected
    | true =>
      simp only [d86028, d87187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4954 q selected
  have h3 (q : Pattern) (selected : d86029 q = 0) : d87300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86029, d87300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86029, d87300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86034 q = 0) : d87305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86034, d87305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4981 q selected
    | true =>
      simp only [d86034, d87305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86035 q = 0) : d87306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86035, d87306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86035, d87306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86036 q = 0) : d87307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86036, d87307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86036, d87307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86037 q = 0) : d87308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86037, d87308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86037, d87308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86038 q = 0) : d87309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86038, d87309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86038, d87309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86039 q = 0) : d87310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86039, d87310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86039, d87310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro4983 (p : Pattern) (selected : d86045 p = 0) : d87316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85768 q = 0) : d87087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d85768, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4932 q selected
    | true =>
      simp only [d85768, d87087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86041 q = 0) : d87312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86041, d87312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86041, d87312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86042 q = 0) : d87313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86042, d87313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86042, d87313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86043 q = 0) : d87314 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86043, d87314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86043, d87314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86044 q = 0) : d87315 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86044, d87315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86044, d87315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86045 q = 0) : d87316 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86045, d87316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86045, d87316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4984 (p : Pattern) (selected : d86051 p = 0) : d87322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85915 q = 0) : d87210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85915, d87210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85915, d87210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4958 q selected
  have h2 (q : Pattern) (selected : d85916 q = 0) : d87211 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85916, d87211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d85916, d87211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d85922 q = 0) : d87217 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85922, d87217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4958 q selected
    | true =>
      simp only [d85922, d87217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4959 q selected
  have h4 (q : Pattern) (selected : d85923 q = 0) : d87218 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85923, d87218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d85923, d87218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85924 q = 0) : d87219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85924, d87219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85924, d87219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85991 q = 0) : d87273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85991, d87273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4967 q selected
    | true =>
      simp only [d85991, d87273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4973 q selected
  have h7 (q : Pattern) (selected : d85993 q = 0) : d87275 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85993, d87275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4974 q selected
    | true =>
      simp only [d85993, d87275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4936 q selected
  have h8 (q : Pattern) (selected : d85994 q = 0) : d87276 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85994, d87276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d85994, d87276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d85995 q = 0) : d87277 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85995, d87277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d85995, d87277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d85996 q = 0) : d87278 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85996, d87278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d85996, d87278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86000 q = 0) : d87282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86000, d87282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86000, d87282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4975 q selected
  have h12 (q : Pattern) (selected : d86002 q = 0) : d87284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86002, d87284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86002, d87284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4976 q selected
  have h13 (q : Pattern) (selected : d86003 q = 0) : d87285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86003, d87285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86003, d87285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86004 q = 0) : d87286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86004, d87286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86004, d87286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d86005 q = 0) : d87287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86005, d87287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d86005, d87287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d86006 q = 0) : d87288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86006, d87288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86006, d87288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86040 q = 0) : d87311 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86040, d87311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86040, d87311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4982 q selected
  have h18 (q : Pattern) (selected : d86046 q = 0) : d87317 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86046, d87317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86046, d87317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4983 q selected
  have h19 (q : Pattern) (selected : d86047 q = 0) : d87318 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86047, d87318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86047, d87318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d86048 q = 0) : d87319 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86048, d87319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d86048, d87319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d86049 q = 0) : d87320 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86049, d87320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d86049, d87320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d86050 q = 0) : d87321 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86050, d87321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d86050, d87321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d86051 q = 0) : d87322 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86051, d87322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86051, d87322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro4985 (p : Pattern) (selected : d86057 p = 0) : d87328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86052 q = 0) : d87323 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86052, d87323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86052, d87323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4984 q selected
  have h2 (q : Pattern) (selected : d86053 q = 0) : d87324 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86053, d87324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86053, d87324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86054 q = 0) : d87325 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86054, d87325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86054, d87325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86055 q = 0) : d87326 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86055, d87326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86055, d87326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86056 q = 0) : d87327 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86056, d87327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86056, d87327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86057 q = 0) : d87328 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86057, d87328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86057, d87328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4986 (p : Pattern) (selected : d86064 p = 0) : d87335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86059 q = 0) : d87330 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h2 (q : Pattern) (selected : d86060 q = 0) : d87331 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86061 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h4 (q : Pattern) (selected : d86062 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86063 q = 0) : d87334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86064 q = 0) : d87335 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86064, d87335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86064, d87335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4987 (p : Pattern) (selected : d86068 p = 0) : d87339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86061 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h2 (q : Pattern) (selected : d86062 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86067 q = 0) : d87338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86067, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86067, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86068 q = 0) : d87339 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86068, d87339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86068, d87339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro4988 (p : Pattern) (selected : d86074 p = 0) : d87345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86071 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86072 q = 0) : d87343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86073 q = 0) : d87344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86073, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86073, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86074 q = 0) : d87345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86074, d87345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86074, d87345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4989 (p : Pattern) (selected : d86078 p = 0) : d87349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86075 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86076 q = 0) : d87347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86077 q = 0) : d87348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86077, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86077, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86078 q = 0) : d87349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86078, d87349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86078, d87349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4990 (p : Pattern) (selected : d86084 p = 0) : d87355 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86079 q = 0) : d87350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86079, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4988 q selected
    | true =>
      simp only [d86079, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4989 q selected
  have h2 (q : Pattern) (selected : d86080 q = 0) : d87351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86080, d87351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86080, d87351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86081 q = 0) : d87352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86081, d87352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86081, d87352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86082 q = 0) : d87353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86082, d87353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86082, d87353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86083 q = 0) : d87354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86083, d87354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86083, d87354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86084 q = 0) : d87355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86084, d87355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86084, d87355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4991 (p : Pattern) (selected : d86087 p = 0) : d87358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86071 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86072 q = 0) : d87343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86073 q = 0) : d87344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86073, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86073, d87344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86087 q = 0) : d87358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86087, d87358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86087, d87358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro4992 (p : Pattern) (selected : d86088 p = 0) : d87359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86075 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86076 q = 0) : d87347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86077 q = 0) : d87348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86077, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86077, d87348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86088 q = 0) : d87359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86088, d87359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86088, d87359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4993 (p : Pattern) (selected : d86094 p = 0) : d87365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86079 q = 0) : d87350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86079, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4988 q selected
    | true =>
      simp only [d86079, d87350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4989 q selected
  have h2 (q : Pattern) (selected : d86080 q = 0) : d87351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86080, d87351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86080, d87351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86081 q = 0) : d87352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86081, d87352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86081, d87352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86082 q = 0) : d87353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86082, d87353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86082, d87353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86083 q = 0) : d87354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86083, d87354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86083, d87354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86089 q = 0) : d87360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86089, d87360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4991 q selected
    | true =>
      simp only [d86089, d87360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4992 q selected
  have h7 (q : Pattern) (selected : d86090 q = 0) : d87361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86090, d87361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86090, d87361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86091 q = 0) : d87362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86091, d87362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86091, d87362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d86092 q = 0) : d87363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86092, d87363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86092, d87363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86093 q = 0) : d87364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86093, d87364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86093, d87364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86094 q = 0) : d87365 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86094, d87365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86094, d87365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro4994 (p : Pattern) (selected : d86099 p = 0) : d87370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86071 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86072 q = 0) : d87343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86072, d87343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86098 q = 0) : d87369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86098, d87369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86098, d87369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86099 q = 0) : d87370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86099, d87370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86099, d87370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4995 (p : Pattern) (selected : d86101 p = 0) : d87372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86075 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86076 q = 0) : d87347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86076, d87347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86100 q = 0) : d87371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86100, d87371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86100, d87371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86101 q = 0) : d87372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86101, d87372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86101, d87372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4996 (p : Pattern) (selected : d86108 p = 0) : d87379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86071 q = 0) : d87342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86071, d87342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86106 q = 0) : d87377 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86106, d87377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86106, d87377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86107 q = 0) : d87378 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86107, d87378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86107, d87378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86108 q = 0) : d87379 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86108, d87379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86108, d87379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro4997 (p : Pattern) (selected : d86111 p = 0) : d87382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86069 q = 0) : d87340 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4987 q selected
    | true =>
      simp only [d86069, d87340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86070 q = 0) : d87341 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86070, d87341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86075 q = 0) : d87346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86075, d87346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86109 q = 0) : d87380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86109, d87380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86109, d87380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86110 q = 0) : d87381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86110, d87381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86110, d87381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86111 q = 0) : d87382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86111, d87382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86111, d87382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro4998 (p : Pattern) (selected : d86118 p = 0) : d87389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86115 q = 0) : d87386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86115, d87386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86115, d87386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
  have h2 (q : Pattern) (selected : d86116 q = 0) : d87387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86116, d87387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86116, d87387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86059 q = 0) : d87330 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h4 (q : Pattern) (selected : d86060 q = 0) : d87331 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86117 q = 0) : d87388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86117, d87388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86117, d87388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86118 q = 0) : d87389 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86118, d87389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86118, d87389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro4999 (p : Pattern) (selected : d86124 p = 0) : d87395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86119 q = 0) : d87390 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86119, d87390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4998 q selected
    | true =>
      simp only [d86119, d87390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86120 q = 0) : d87391 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86120, d87391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86120, d87391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86065 q = 0) : d87336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4986 q selected
    | true =>
      simp only [d86065, d87336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86066 q = 0) : d87337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86066, d87337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86121 q = 0) : d87392 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86121, d87392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86121, d87392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86122 q = 0) : d87393 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86122, d87393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86122, d87393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86123 q = 0) : d87394 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86123, d87394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86123, d87394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86124 q = 0) : d87395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86124, d87395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86124, d87395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
