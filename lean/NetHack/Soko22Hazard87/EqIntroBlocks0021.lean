import NetHack.Soko22Hazard87.EqIntroBlocks0020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro5250 (p : Pattern) (selected : d86714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86707 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro133 q selected
  have h2 (q : Pattern) (selected : d86708 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86714 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5251 (p : Pattern) (selected : d86720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86711 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5249 q selected
    | true =>
      simp only [d86711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86712 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86715 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5250 q selected
    | true =>
      simp only [d86715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86716 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86717 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86718 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86719 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86720 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5252 (p : Pattern) (selected : d86724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86715 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5250 q selected
    | true =>
      simp only [d86715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86716 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86721 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5253 (p : Pattern) (selected : d86736 p = 1) : d89496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86704 q = 1) : d86704 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5251 q selected
    | true =>
      simp only [d86725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5252 q selected
  have h3 (q : Pattern) (selected : d86726 q = 1) : d89492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86726, d89492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86726, d89492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86732 q = 1) : d86732 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86733 q = 1) : d89493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86733, d89493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86733, d89493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86734 q = 1) : d89494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86734, d89494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86734, d89494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86735 q = 1) : d89495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86735, d89495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86735, d89495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86736 q = 1) : d89496 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86736, d89496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86736, d89496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5254 (p : Pattern) (selected : d86753 p = 1) : d89502 p = 1 := by
  have h0 (q : Pattern) (selected : d86566 q = 1) : d86566 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86651 q = 1) : d89480 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86651, d89480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5244 q selected
    | true =>
      simp only [d86651, d89480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5247 q selected
  have h2 (q : Pattern) (selected : d86664 q = 1) : d86664 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86665 q = 1) : d89481 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86665, d89481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86665, d89481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86666 q = 1) : d89482 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86666, d89482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86666, d89482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86667 q = 1) : d89483 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86667, d89483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86667, d89483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86671 q = 1) : d89487 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86671, d89487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86671, d89487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5248 q selected
  have h8 (q : Pattern) (selected : d86673 q = 1) : d86673 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d86674 q = 1) : d89488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86674, d89488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86674, d89488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86675 q = 1) : d89489 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86675, d89489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86675, d89489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d86676 q = 1) : d89490 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86676, d89490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86676, d89490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d86677 q = 1) : d89491 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86677, d89491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86677, d89491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d86737 q = 1) : d89497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86737, d89497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86737, d89497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5253 q selected
  have h14 (q : Pattern) (selected : d86748 q = 1) : d86748 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86749 q = 1) : d89498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86749, d89498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86749, d89498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86750 q = 1) : d89499 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86750, d89499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86750, d89499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d86751 q = 1) : d89500 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86751, d89500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86751, d89500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d86752 q = 1) : d89501 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86752, d89501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86752, d89501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d86753 q = 1) : d89502 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86753, d89502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d86753, d89502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro5255 (p : Pattern) (selected : d86759 p = 1) : d89508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86754 q = 1) : d89503 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86754, d89503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86754, d89503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5254 q selected
  have h2 (q : Pattern) (selected : d86755 q = 1) : d89504 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86755, d89504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86755, d89504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86756 q = 1) : d89505 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86756, d89505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86756, d89505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86757 q = 1) : d89506 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86757, d89506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86757, d89506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86758 q = 1) : d89507 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86758, d89507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86758, d89507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86759 q = 1) : d89508 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86759, d89508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86759, d89508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5256 (p : Pattern) (selected : d86836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86831 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro156 q selected
  have h2 (q : Pattern) (selected : d86832 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro158 q selected
  have h4 (q : Pattern) (selected : d86834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86836 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5257 (p : Pattern) (selected : d86840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86833 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro158 q selected
  have h2 (q : Pattern) (selected : d86834 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5258 (p : Pattern) (selected : d86846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5256 q selected
    | true =>
      simp only [d86837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5257 q selected
    | true =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5259 (p : Pattern) (selected : d86850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5257 q selected
    | true =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86847 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86848 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86850 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5260 (p : Pattern) (selected : d86862 p = 1) : d89517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86810 q = 1) : d86810 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86819 q = 1) : d86819 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86830 q = 1) : d86830 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d86851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5258 q selected
    | true =>
      simp only [d86851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5259 q selected
  have h5 (q : Pattern) (selected : d86852 q = 1) : d89513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86852, d89513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86852, d89513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86858 q = 1) : d86858 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d86859 q = 1) : d89514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86859, d89514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86859, d89514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86860 q = 1) : d89515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86860, d89515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86860, d89515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86861 q = 1) : d89516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86861, d89516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86861, d89516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86862 q = 1) : d89517 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86862, d89517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86862, d89517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro5261 (p : Pattern) (selected : d86876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5256 q selected
    | true =>
      simp only [d86837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5257 q selected
    | true =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86876 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5262 (p : Pattern) (selected : d86877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5257 q selected
    | true =>
      simp only [d86841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86847 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86848 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86849 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86877 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5263 (p : Pattern) (selected : d86886 p = 1) : d89522 p = 1 := by
  have h0 (q : Pattern) (selected : d86810 q = 1) : d86810 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86819 q = 1) : d86819 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86830 q = 1) : d86830 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86851 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5258 q selected
    | true =>
      simp only [d86851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5259 q selected
  have h4 (q : Pattern) (selected : d86852 q = 1) : d89513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86852, d89513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86852, d89513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86858 q = 1) : d86858 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d86859 q = 1) : d89514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86859, d89514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86859, d89514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86860 q = 1) : d89515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86860, d89515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86860, d89515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86861 q = 1) : d89516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86861, d89516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86861, d89516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86868 q = 1) : d86868 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d86873 q = 1) : d86873 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d86875 q = 1) : d86875 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d86878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5261 q selected
    | true =>
      simp only [d86878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5262 q selected
  have h13 (q : Pattern) (selected : d86879 q = 1) : d89518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86879, d89518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d86879, d89518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86882 q = 1) : d86882 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86883 q = 1) : d89519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86883, d89519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86883, d89519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86884 q = 1) : d89520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86884, d89520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86884, d89520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d86885 q = 1) : d89521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86885, d89521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86885, d89521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d86886 q = 1) : d89522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86886, d89522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d86886, d89522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro5264 (p : Pattern) (selected : d86906 p = 1) : d89529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86875 q = 1) : d86875 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5261 q selected
    | true =>
      simp only [d86878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5262 q selected
  have h3 (q : Pattern) (selected : d86879 q = 1) : d89518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86879, d89518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86879, d89518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86882 q = 1) : d86882 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86883 q = 1) : d89519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86883, d89519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86883, d89519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86904 q = 1) : d89527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86904, d89527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86904, d89527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86905 q = 1) : d89528 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86905, d89528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86905, d89528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86906 q = 1) : d89529 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86906, d89529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86906, d89529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5265 (p : Pattern) (selected : d86946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86941 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro169 q selected
  have h2 (q : Pattern) (selected : d86942 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro170 q selected
  have h4 (q : Pattern) (selected : d86944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86945 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86946 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5266 (p : Pattern) (selected : d86950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro170 q selected
  have h2 (q : Pattern) (selected : d86944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86949 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d86950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro5267 (p : Pattern) (selected : d86956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5265 q selected
    | true =>
      simp only [d86947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5266 q selected
    | true =>
      simp only [d86951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d86955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d86956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro5268 (p : Pattern) (selected : d86960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d86951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5266 q selected
    | true =>
      simp only [d86951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d86952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d86952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d86957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d86958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d86958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d86959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d86959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d86960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d86960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d86960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5269 (p : Pattern) (selected : d86972 p = 1) : d89539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86940 q = 1) : d86940 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d86961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5267 q selected
    | true =>
      simp only [d86961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5268 q selected
  have h3 (q : Pattern) (selected : d86962 q = 1) : d89535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d86962, d89535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86962, d89535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86968 q = 1) : d86968 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86969 q = 1) : d89536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86969, d89536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86969, d89536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86970 q = 1) : d89537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d86970, d89537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86970, d89537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86971 q = 1) : d89538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d86971, d89538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86971, d89538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86972 q = 1) : d89539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d86972, d89539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86972, d89539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro5270 (p : Pattern) (selected : d86989 p = 1) : d89545 p = 1 := by
  have h0 (q : Pattern) (selected : d86802 q = 1) : d86802 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86887 q = 1) : d89523 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86887, d89523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5260 q selected
    | true =>
      simp only [d86887, d89523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5263 q selected
  have h2 (q : Pattern) (selected : d86900 q = 1) : d86900 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d86901 q = 1) : d89524 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86901, d89524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86901, d89524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d86902 q = 1) : d89525 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86902, d89525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86902, d89525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86903 q = 1) : d89526 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86903, d89526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86903, d89526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86907 q = 1) : d89530 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86907, d89530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86907, d89530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5264 q selected
  have h8 (q : Pattern) (selected : d86909 q = 1) : d86909 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d86910 q = 1) : d89531 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86910, d89531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d86910, d89531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86911 q = 1) : d89532 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86911, d89532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d86911, d89532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d86912 q = 1) : d89533 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86912, d89533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d86912, d89533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d86913 q = 1) : d89534 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86913, d89534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86913, d89534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d86973 q = 1) : d89540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d86973, d89540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86973, d89540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5269 q selected
  have h14 (q : Pattern) (selected : d86984 q = 1) : d86984 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d86985 q = 1) : d89541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d86985, d89541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d86985, d89541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d86986 q = 1) : d89542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d86986, d89542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d86986, d89542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d86987 q = 1) : d89543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d86987, d89543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d86987, d89543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d86988 q = 1) : d89544 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d86988, d89544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d86988, d89544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d86989 q = 1) : d89545 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d86989, d89545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d86989, d89545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro5271 (p : Pattern) (selected : d86995 p = 1) : d89551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d86990 q = 1) : d89546 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d86990, d89546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86990, d89546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5270 q selected
  have h2 (q : Pattern) (selected : d86991 q = 1) : d89547 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d86991, d89547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86991, d89547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86992 q = 1) : d89548 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d86992, d89548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86992, d89548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86993 q = 1) : d89549 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d86993, d89549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86993, d89549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86994 q = 1) : d89550 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d86994, d89550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86994, d89550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86995 q = 1) : d89551 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d86995, d89551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86995, d89551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5272 (p : Pattern) (selected : d87001 p = 1) : d89557 p = 1 := by
  have h0 (q : Pattern) (selected : d86058 q = 1) : d89386 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86058, d89386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5196 q selected
    | true =>
      simp only [d86058, d89386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5207 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d86291 q = 1) : d89426 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86291, d89426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86291, d89426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5223 q selected
  have h3 (q : Pattern) (selected : d86292 q = 1) : d89427 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86292, d89427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86292, d89427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d86525 q = 1) : d89467 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86525, d89467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86525, d89467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5239 q selected
  have h5 (q : Pattern) (selected : d86526 q = 1) : d89468 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86526, d89468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86526, d89468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86527 q = 1) : d89469 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d86527, d89469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d86527, d89469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d86760 q = 1) : d89509 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86760, d89509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86760, d89509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5255 q selected
  have h8 (q : Pattern) (selected : d86761 q = 1) : d89510 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86761, d89510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86761, d89510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d86762 q = 1) : d89511 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d86762, d89511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86762, d89511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d86763 q = 1) : d89512 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d86763, d89512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d86763, d89512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d86996 q = 1) : d89552 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d86996, d89552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86996, d89552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5271 q selected
  have h12 (q : Pattern) (selected : d86997 q = 1) : d89553 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d86997, d89553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86997, d89553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d86998 q = 1) : d89554 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d86998, d89554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86998, d89554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d86999 q = 1) : d89555 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d86999, d89555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d86999, d89555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d87000 q = 1) : d89556 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d87000, d89556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d87000, d89556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d87001 q = 1) : d89557 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d87001, d89557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d87001, d89557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro5273 (p : Pattern) (selected : d87007 p = 1) : d89563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d87002 q = 1) : d89558 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d87002, d89558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5272 q selected
    | true =>
      simp only [d87002, d89558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87003 q = 1) : d89559 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d87003, d89559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87003, d89559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87004 q = 1) : d89560 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d87004, d89560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87004, d89560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87005 q = 1) : d89561 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d87005, d89561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87005, d89561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87006 q = 1) : d89562 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d87006, d89562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87006, d89562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87007 q = 1) : d89563 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d87007, d89563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87007, d89563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5274 (p : Pattern) (selected : d87013 p = 1) : d89569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d87008 q = 1) : d89564 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d87008, d89564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5273 q selected
    | true =>
      simp only [d87008, d89564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87009 q = 1) : d89565 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d87009, d89565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87009, d89565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87010 q = 1) : d89566 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d87010, d89566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87010, d89566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87011 q = 1) : d89567 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d87011, d89567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87011, d89567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87012 q = 1) : d89568 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d87012, d89568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87012, d89568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87013 q = 1) : d89569 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d87013, d89569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87013, d89569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5275 (p : Pattern) (selected : d87019 p = 1) : d89575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d87014 q = 1) : d89570 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d87014, d89570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5274 q selected
    | true =>
      simp only [d87014, d89570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87015 q = 1) : d89571 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d87015, d89571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87015, d89571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87016 q = 1) : d89572 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d87016, d89572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87016, d89572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87017 q = 1) : d89573 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d87017, d89573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87017, d89573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87018 q = 1) : d89574 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d87018, d89574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87018, d89574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87019 q = 1) : d89575 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d87019, d89575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87019, d89575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5276 (p : Pattern) (selected : d87025 p = 1) : d89581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d87020 q = 1) : d89576 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d87020, d89576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5275 q selected
    | true =>
      simp only [d87020, d89576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87021 q = 1) : d89577 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d87021, d89577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87021, d89577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87022 q = 1) : d89578 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d87022, d89578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87022, d89578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87023 q = 1) : d89579 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d87023, d89579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87023, d89579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87024 q = 1) : d89580 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d87024, d89580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87024, d89580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87025 q = 1) : d89581 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d87025, d89581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87025, d89581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5277 (p : Pattern) (selected : d87031 p = 1) : d89587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d87026 q = 1) : d89582 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d87026, d89582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5276 q selected
    | true =>
      simp only [d87026, d89582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87027 q = 1) : d89583 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d87027, d89583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87027, d89583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87028 q = 1) : d89584 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d87028, d89584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87028, d89584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87029 q = 1) : d89585 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d87029, d89585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87029, d89585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87030 q = 1) : d89586 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d87030, d89586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87030, d89586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87031 q = 1) : d89587 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d87031, d89587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87031, d89587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5278 (p : Pattern) (selected : d87037 p = 1) : d89593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d87032 q = 1) : d89588 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d87032, d89588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5277 q selected
    | true =>
      simp only [d87032, d89588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87033 q = 1) : d89589 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d87033, d89589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87033, d89589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87034 q = 1) : d89590 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d87034, d89590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87034, d89590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87035 q = 1) : d89591 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d87035, d89591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87035, d89591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87036 q = 1) : d89592 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d87036, d89592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87036, d89592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87037 q = 1) : d89593 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d87037, d89593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87037, d89593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5279 (p : Pattern) (selected : d87043 p = 1) : d89599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d87038 q = 1) : d89594 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d87038, d89594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5278 q selected
    | true =>
      simp only [d87038, d89594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d87039 q = 1) : d89595 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d87039, d89595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d87039, d89595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d87040 q = 1) : d89596 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d87040, d89596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d87040, d89596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d87041 q = 1) : d89597 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d87041, d89597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d87041, d89597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d87042 q = 1) : d89598 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d87042, d89598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d87042, d89598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d87043 q = 1) : d89599 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d87043, d89599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d87043, d89599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5280 (p : Pattern) (selected : d89611 p = 0) : d90849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89608 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89609 q = 0) : d90847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89610 q = 0) : d90848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89610, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89610, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89611 q = 0) : d90849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89611, d90849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89611, d90849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5281 (p : Pattern) (selected : d89617 p = 0) : d90855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89613 q = 0) : d90851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89614 q = 0) : d90852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89614, d90852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89614, d90852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89615 q = 0) : d90853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89615, d90853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89615, d90853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89616 q = 0) : d90854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89616, d90854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89616, d90854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89617 q = 0) : d90855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89617, d90855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89617, d90855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5282 (p : Pattern) (selected : d89618 p = 0) : d90856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89608 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89609 q = 0) : d90847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89610 q = 0) : d90848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89610, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89610, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89618 q = 0) : d90856 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89618, d90856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89618, d90856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5283 (p : Pattern) (selected : d89624 p = 0) : d90862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89613 q = 0) : d90851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89614 q = 0) : d90852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89614, d90852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89614, d90852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89615 q = 0) : d90853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89615, d90853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89615, d90853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89616 q = 0) : d90854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89616, d90854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89616, d90854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89619 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
    | true =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d89620 q = 0) : d90858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89621 q = 0) : d90859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89621, d90859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89621, d90859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89622 q = 0) : d90860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89622, d90860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89622, d90860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89623 q = 0) : d90861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89623, d90861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89623, d90861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89624 q = 0) : d90862 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89624, d90862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89624, d90862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5284 (p : Pattern) (selected : d89629 p = 0) : d90867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89619 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
    | true =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89620 q = 0) : d90858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89621 q = 0) : d90859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89621, d90859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89621, d90859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89622 q = 0) : d90860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89622, d90860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89622, d90860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89623 q = 0) : d90861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89623, d90861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89623, d90861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89629 q = 0) : d90867 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89629, d90867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89629, d90867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5285 (p : Pattern) (selected : d89638 p = 0) : d90876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d78 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro196 q selected
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89635 q = 0) : d90873 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89635, d90873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89635, d90873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89636 q = 0) : d90874 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89636, d90874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89636, d90874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89637 q = 0) : d90875 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89637, d90875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89637, d90875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89638 q = 0) : d90876 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89638, d90876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89638, d90876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5286 (p : Pattern) (selected : d89644 p = 0) : d90882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89639 q = 0) : d90877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89639, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5285 q selected
    | true =>
      simp only [d89639, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89640 q = 0) : d90878 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89640, d90878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89640, d90878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89641 q = 0) : d90879 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89641, d90879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89641, d90879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89642 q = 0) : d90880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89642, d90880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89642, d90880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89643 q = 0) : d90881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89643, d90881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89643, d90881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89644 q = 0) : d90882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89644, d90882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89644, d90882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5287 (p : Pattern) (selected : d89650 p = 0) : d90888 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89625 q = 0) : d90863 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89625, d90863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5281 q selected
    | true =>
      simp only [d89625, d90863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5283 q selected
  have h2 (q : Pattern) (selected : d89626 q = 0) : d90864 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89626, d90864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89626, d90864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89627 q = 0) : d90865 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89627, d90865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89627, d90865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89628 q = 0) : d90866 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89628, d90866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89628, d90866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89630 q = 0) : d90868 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89630, d90868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89630, d90868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5284 q selected
  have h6 (q : Pattern) (selected : d89631 q = 0) : d90869 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89631, d90869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89631, d90869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d89632 q = 0) : d90870 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89632, d90870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89632, d90870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89633 q = 0) : d90871 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89633, d90871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89633, d90871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89634 q = 0) : d90872 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89634, d90872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89634, d90872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89645 q = 0) : d90883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89645, d90883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89645, d90883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5286 q selected
  have h11 (q : Pattern) (selected : d89646 q = 0) : d90884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89646, d90884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89646, d90884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d89647 q = 0) : d90885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89647, d90885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89647, d90885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89648 q = 0) : d90886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89648, d90886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d89648, d90886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d89649 q = 0) : d90887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89649, d90887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d89649, d90887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d89650 q = 0) : d90888 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89650, d90888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d89650, d90888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro5288 (p : Pattern) (selected : d89659 p = 0) : d90897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89655 q = 0) : d90893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89656 q = 0) : d90894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89657 q = 0) : d90895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89658 q = 0) : d90896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89659 q = 0) : d90897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89659, d90897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89659, d90897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5289 (p : Pattern) (selected : d89666 p = 0) : d90904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89655 q = 0) : d90893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89656 q = 0) : d90894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89657 q = 0) : d90895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89658 q = 0) : d90896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89619 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
    | true =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d89662 q = 0) : d90900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89662, d90900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89662, d90900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89663 q = 0) : d90901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89663, d90901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89663, d90901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89664 q = 0) : d90902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89664, d90902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89664, d90902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89665 q = 0) : d90903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89665, d90903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89665, d90903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89666 q = 0) : d90904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89666, d90904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89666, d90904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5290 (p : Pattern) (selected : d89671 p = 0) : d90909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89608 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89609 q = 0) : d90847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89670 q = 0) : d90908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89670, d90908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89670, d90908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89671 q = 0) : d90909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89671, d90909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89671, d90909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5291 (p : Pattern) (selected : d89678 p = 0) : d90916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89608 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89676 q = 0) : d90914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89676, d90914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89676, d90914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89677 q = 0) : d90915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89677, d90915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89677, d90915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89678 q = 0) : d90916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89678, d90916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89678, d90916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5292 (p : Pattern) (selected : d89685 p = 0) : d90923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89682 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89683 q = 0) : d90921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89684 q = 0) : d90922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89684, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89684, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89685 q = 0) : d90923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89685, d90923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89685, d90923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5293 (p : Pattern) (selected : d89690 p = 0) : d90849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89687 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89687, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89687, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89688 q = 0) : d90847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89688, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89688, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89689 q = 0) : d90848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89689, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89689, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89690 q = 0) : d90849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89690, d90849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89690, d90849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5294 (p : Pattern) (selected : d89696 p = 0) : d90929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89672 q = 0) : d90910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89672, d90910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5290 q selected
    | true =>
      simp only [d89672, d90910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89673 q = 0) : d90911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89673, d90911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89673, d90911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89674 q = 0) : d90912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89674, d90912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89674, d90912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89675 q = 0) : d90913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89675, d90913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89675, d90913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89679 q = 0) : d90917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89679, d90917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5291 q selected
    | true =>
      simp only [d89679, d90917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89680 q = 0) : d90918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89680, d90918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89680, d90918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89681 q = 0) : d90919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89681, d90919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89681, d90919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89686 q = 0) : d90924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5292 q selected
    | true =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
  have h9 (q : Pattern) (selected : d89691 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89691, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5293 q selected
    | true =>
      simp only [d89691, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d89692 q = 0) : d90925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89692, d90925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89692, d90925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d89613 q = 0) : d90851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89693 q = 0) : d90926 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89693, d90926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89693, d90926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89694 q = 0) : d90927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89694, d90927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89694, d90927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d89695 q = 0) : d90928 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89695, d90928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89695, d90928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d89696 q = 0) : d90929 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89696, d90929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89696, d90929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5295 (p : Pattern) (selected : d89697 p = 0) : d90930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89608 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89609 q = 0) : d90847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89609, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89670 q = 0) : d90908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89670, d90908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89670, d90908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89697 q = 0) : d90930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89697, d90930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89697, d90930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5296 (p : Pattern) (selected : d89702 p = 0) : d90935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89608 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89608, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89676 q = 0) : d90914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89676, d90914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89676, d90914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89677 q = 0) : d90915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89677, d90915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89677, d90915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89702 q = 0) : d90935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89702, d90935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89702, d90935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5297 (p : Pattern) (selected : d89706 p = 0) : d90939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89682 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89683 q = 0) : d90921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89684 q = 0) : d90922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89684, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89684, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89706 q = 0) : d90939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89706, d90939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89706, d90939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5298 (p : Pattern) (selected : d89708 p = 0) : d90856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89687 q = 0) : d90846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89687, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89687, d90846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89688 q = 0) : d90847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89688, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89688, d90847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89689 q = 0) : d90848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89689, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89689, d90848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89708 q = 0) : d90856 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89708, d90856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89708, d90856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5299 (p : Pattern) (selected : d89714 p = 0) : d90945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89672 q = 0) : d90910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89672, d90910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5290 q selected
    | true =>
      simp only [d89672, d90910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89673 q = 0) : d90911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89673, d90911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89673, d90911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89674 q = 0) : d90912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89674, d90912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89674, d90912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89675 q = 0) : d90913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89675, d90913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89675, d90913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89679 q = 0) : d90917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89679, d90917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5291 q selected
    | true =>
      simp only [d89679, d90917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89680 q = 0) : d90918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89680, d90918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89680, d90918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89681 q = 0) : d90919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89681, d90919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89681, d90919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89686 q = 0) : d90924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5292 q selected
    | true =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
  have h9 (q : Pattern) (selected : d89691 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89691, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5293 q selected
    | true =>
      simp only [d89691, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d89692 q = 0) : d90925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89692, d90925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89692, d90925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d89613 q = 0) : d90851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89613, d90851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89693 q = 0) : d90926 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89693, d90926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89693, d90926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89694 q = 0) : d90927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89694, d90927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89694, d90927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d89695 q = 0) : d90928 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89695, d90928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89695, d90928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d89698 q = 0) : d90931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89698, d90931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5295 q selected
    | true =>
      simp only [d89698, d90931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d89699 q = 0) : d90932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89699, d90932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89699, d90932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d89700 q = 0) : d90933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89700, d90933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d89700, d90933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d89701 q = 0) : d90934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89701, d90934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89701, d90934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d89703 q = 0) : d90936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89703, d90936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5296 q selected
    | true =>
      simp only [d89703, d90936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d89704 q = 0) : d90937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89704, d90937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89704, d90937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d89705 q = 0) : d90938 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89705, d90938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d89705, d90938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d89707 q = 0) : d90940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89707, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5297 q selected
    | true =>
      simp only [d89707, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
  have h24 (q : Pattern) (selected : d89709 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89709, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5298 q selected
    | true =>
      simp only [d89709, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d89710 q = 0) : d90941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89710, d90941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d89710, d90941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d89619 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
    | true =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d89620 q = 0) : d90858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d89711 q = 0) : d90942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89711, d90942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d89711, d90942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d89712 q = 0) : d90943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89712, d90943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d89712, d90943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d89713 q = 0) : d90944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89713, d90944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d89713, d90944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d89714 q = 0) : d90945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89714, d90945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d89714, d90945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5300 (p : Pattern) (selected : d89716 p = 0) : d90947 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89655 q = 0) : d90893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89656 q = 0) : d90894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89657 q = 0) : d90895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89658 q = 0) : d90896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89716 q = 0) : d90947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89716, d90947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89716, d90947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5301 (p : Pattern) (selected : d89723 p = 0) : d90954 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89707 q = 0) : d90940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89707, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5297 q selected
    | true =>
      simp only [d89707, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
  have h2 (q : Pattern) (selected : d89709 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89709, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5298 q selected
    | true =>
      simp only [d89709, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89710 q = 0) : d90941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89710, d90941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89710, d90941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89619 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
    | true =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89620 q = 0) : d90858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89620, d90858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89711 q = 0) : d90942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89711, d90942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89711, d90942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89721 q = 0) : d90952 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89721, d90952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89721, d90952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89722 q = 0) : d90953 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89722, d90953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89722, d90953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89723 q = 0) : d90954 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89723, d90954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89723, d90954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5302 (p : Pattern) (selected : d89732 p = 0) : d90963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d238 q = 0) : d52056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro223 q selected
    | true =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d78 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro196 q selected
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89729 q = 0) : d90960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89729, d90960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89729, d90960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89730 q = 0) : d90961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89730, d90961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89730, d90961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89731 q = 0) : d90962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89731, d90962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89731, d90962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89732 q = 0) : d90963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89732, d90963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89732, d90963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5303 (p : Pattern) (selected : d89737 p = 0) : d90876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d257 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro226 q selected
    | true =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89734 q = 0) : d90873 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89734, d90873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89734, d90873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89735 q = 0) : d90874 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89735, d90874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89735, d90874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89736 q = 0) : d90875 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89736, d90875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89736, d90875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89737 q = 0) : d90876 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89737, d90876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89737, d90876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5304 (p : Pattern) (selected : d89743 p = 0) : d90969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89733 q = 0) : d90964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89733, d90964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5302 q selected
    | true =>
      simp only [d89733, d90964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5285 q selected
  have h2 (q : Pattern) (selected : d89738 q = 0) : d90877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89738, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5303 q selected
    | true =>
      simp only [d89738, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89739 q = 0) : d90965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89739, d90965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89739, d90965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89639 q = 0) : d90877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89639, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5285 q selected
    | true =>
      simp only [d89639, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89640 q = 0) : d90878 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89640, d90878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89640, d90878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89740 q = 0) : d90966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89740, d90966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89740, d90966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89741 q = 0) : d90967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89741, d90967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89741, d90967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89742 q = 0) : d90968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89742, d90968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89742, d90968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89743 q = 0) : d90969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89743, d90969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89743, d90969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5305 (p : Pattern) (selected : d89749 p = 0) : d90975 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89660 q = 0) : d90898 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89660, d90898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89660, d90898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5288 q selected
  have h2 (q : Pattern) (selected : d89661 q = 0) : d90899 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89661, d90899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89661, d90899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89667 q = 0) : d90905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89667, d90905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5288 q selected
    | true =>
      simp only [d89667, d90905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5289 q selected
  have h4 (q : Pattern) (selected : d89668 q = 0) : d90906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89668, d90906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89668, d90906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89669 q = 0) : d90907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89669, d90907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89669, d90907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89715 q = 0) : d90946 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89715, d90946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5294 q selected
    | true =>
      simp only [d89715, d90946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5299 q selected
  have h7 (q : Pattern) (selected : d89717 q = 0) : d90948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89717, d90948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5300 q selected
    | true =>
      simp only [d89717, d90948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89718 q = 0) : d90949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89718, d90949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89718, d90949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89719 q = 0) : d90950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89719, d90950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89719, d90950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d89720 q = 0) : d90951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89720, d90951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89720, d90951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89724 q = 0) : d90955 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89724, d90955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89724, d90955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5301 q selected
  have h12 (q : Pattern) (selected : d89725 q = 0) : d90956 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89725, d90956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89725, d90956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89726 q = 0) : d90957 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89726, d90957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d89726, d90957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d89727 q = 0) : d90958 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89727, d90958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d89727, d90958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d89728 q = 0) : d90959 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89728, d90959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89728, d90959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d89744 q = 0) : d90970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89744, d90970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89744, d90970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5304 q selected
  have h17 (q : Pattern) (selected : d89745 q = 0) : d90971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89745, d90971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d89745, d90971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d89746 q = 0) : d90972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89746, d90972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d89746, d90972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d89747 q = 0) : d90973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89747, d90973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d89747, d90973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d89748 q = 0) : d90974 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89748, d90974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d89748, d90974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d89749 q = 0) : d90975 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89749, d90975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d89749, d90975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro5306 (p : Pattern) (selected : d89759 p = 0) : d90985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89686 q = 0) : d90924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5292 q selected
    | true =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
  have h2 (q : Pattern) (selected : d89755 q = 0) : d90981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89755, d90981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89755, d90981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89756 q = 0) : d90982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89756, d90982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89756, d90982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89757 q = 0) : d90983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89757, d90983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89757, d90983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89758 q = 0) : d90984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89758, d90984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89758, d90984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89759 q = 0) : d90985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89759, d90985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89759, d90985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5307 (p : Pattern) (selected : d89766 p = 0) : d90992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89686 q = 0) : d90924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5292 q selected
    | true =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
  have h2 (q : Pattern) (selected : d89755 q = 0) : d90981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89755, d90981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89755, d90981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89756 q = 0) : d90982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89756, d90982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89756, d90982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89757 q = 0) : d90983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89757, d90983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89757, d90983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89758 q = 0) : d90984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89758, d90984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89758, d90984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89707 q = 0) : d90940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89707, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5297 q selected
    | true =>
      simp only [d89707, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
  have h7 (q : Pattern) (selected : d89762 q = 0) : d90988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89762, d90988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89762, d90988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89763 q = 0) : d90989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89763, d90989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89763, d90989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89764 q = 0) : d90990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89764, d90990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89764, d90990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89765 q = 0) : d90991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89765, d90991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89765, d90991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89766 q = 0) : d90992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89766, d90992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89766, d90992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5308 (p : Pattern) (selected : d89771 p = 0) : d90997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89682 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89683 q = 0) : d90921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89770 q = 0) : d90996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89770, d90996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89770, d90996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89771 q = 0) : d90997 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89771, d90997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89771, d90997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5309 (p : Pattern) (selected : d89778 p = 0) : d91004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89682 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89776 q = 0) : d91002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89776, d91002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89776, d91002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89777 q = 0) : d91003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89777, d91003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89777, d91003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89778 q = 0) : d91004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89778, d91004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89778, d91004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5310 (p : Pattern) (selected : d89785 p = 0) : d91011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d331 q = 0) : d52130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro237 q selected
    | true =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6740 q = 0) : d81528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4219 q selected
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89782 q = 0) : d91008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89782, d91008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89782, d91008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89783 q = 0) : d91009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89783, d91009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89783, d91009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89784 q = 0) : d91010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89784, d91010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89784, d91010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89785 q = 0) : d91011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89785, d91011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89785, d91011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5311 (p : Pattern) (selected : d89790 p = 0) : d90923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d362 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro242 q selected
    | true =>
      simp only [d362, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89787 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89787, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89787, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89788 q = 0) : d90921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89788, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89788, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89789 q = 0) : d90922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89789, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89789, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89790 q = 0) : d90923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89790, d90923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89790, d90923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5312 (p : Pattern) (selected : d89796 p = 0) : d91017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89793 q = 0) : d91014 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89793, d91014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89793, d91014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89794 q = 0) : d91015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89794, d91015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89794, d91015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89795 q = 0) : d91016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89795, d91016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89795, d91016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89796 q = 0) : d91017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89796, d91017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89796, d91017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5313 (p : Pattern) (selected : d89802 p = 0) : d91023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89772 q = 0) : d90998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89772, d90998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5308 q selected
    | true =>
      simp only [d89772, d90998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5290 q selected
  have h2 (q : Pattern) (selected : d89773 q = 0) : d90999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89773, d90999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89773, d90999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89774 q = 0) : d91000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89774, d91000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89774, d91000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89775 q = 0) : d91001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89775, d91001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89775, d91001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89779 q = 0) : d91005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89779, d91005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5309 q selected
    | true =>
      simp only [d89779, d91005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5291 q selected
  have h6 (q : Pattern) (selected : d89780 q = 0) : d91006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89780, d91006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89780, d91006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89781 q = 0) : d91007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89781, d91007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89781, d91007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89786 q = 0) : d91012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89786, d91012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5310 q selected
    | true =>
      simp only [d89786, d91012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5292 q selected
  have h9 (q : Pattern) (selected : d89791 q = 0) : d90924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89791, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5311 q selected
    | true =>
      simp only [d89791, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5293 q selected
  have h10 (q : Pattern) (selected : d89792 q = 0) : d91013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89792, d91013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89792, d91013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89797 q = 0) : d91018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89797, d91018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5312 q selected
    | true =>
      simp only [d89797, d91018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d89798 q = 0) : d91019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89798, d91019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89798, d91019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89799 q = 0) : d91020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89799, d91020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89799, d91020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89800 q = 0) : d91021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89800, d91021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89800, d91021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d89801 q = 0) : d91022 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89801, d91022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89801, d91022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d89802 q = 0) : d91023 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89802, d91023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89802, d91023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5314 (p : Pattern) (selected : d89803 p = 0) : d91024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89682 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89683 q = 0) : d90921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89683, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89770 q = 0) : d90996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89770, d90996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89770, d90996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89803 q = 0) : d91024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89803, d91024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89803, d91024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5315 (p : Pattern) (selected : d89808 p = 0) : d91029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89682 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89682, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89776 q = 0) : d91002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89776, d91002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89776, d91002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89777 q = 0) : d91003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89777, d91003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89777, d91003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89808 q = 0) : d91029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89808, d91029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89808, d91029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5316 (p : Pattern) (selected : d89812 p = 0) : d91033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d331 q = 0) : d52130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro237 q selected
    | true =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6740 q = 0) : d81528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4219 q selected
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89782 q = 0) : d91008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89782, d91008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89782, d91008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89783 q = 0) : d91009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89783, d91009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89783, d91009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89784 q = 0) : d91010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89784, d91010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89784, d91010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89812 q = 0) : d91033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89812, d91033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89812, d91033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5317 (p : Pattern) (selected : d89814 p = 0) : d90939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d362 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro242 q selected
    | true =>
      simp only [d362, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89787 q = 0) : d90920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89787, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89787, d90920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89788 q = 0) : d90921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89788, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89788, d90921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89789 q = 0) : d90922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89789, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89789, d90922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89814 q = 0) : d90939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89814, d90939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89814, d90939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5318 (p : Pattern) (selected : d89817 p = 0) : d91036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89793 q = 0) : d91014 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89793, d91014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89793, d91014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89794 q = 0) : d91015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89794, d91015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89794, d91015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89795 q = 0) : d91016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89795, d91016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89795, d91016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89817 q = 0) : d91036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89817, d91036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89817, d91036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5319 (p : Pattern) (selected : d89823 p = 0) : d91042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89772 q = 0) : d90998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89772, d90998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5308 q selected
    | true =>
      simp only [d89772, d90998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5290 q selected
  have h2 (q : Pattern) (selected : d89773 q = 0) : d90999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89773, d90999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89773, d90999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89774 q = 0) : d91000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89774, d91000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89774, d91000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89775 q = 0) : d91001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89775, d91001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89775, d91001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89779 q = 0) : d91005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89779, d91005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5309 q selected
    | true =>
      simp only [d89779, d91005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5291 q selected
  have h6 (q : Pattern) (selected : d89780 q = 0) : d91006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89780, d91006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89780, d91006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89781 q = 0) : d91007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89781, d91007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89781, d91007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89786 q = 0) : d91012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89786, d91012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5310 q selected
    | true =>
      simp only [d89786, d91012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5292 q selected
  have h9 (q : Pattern) (selected : d89791 q = 0) : d90924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89791, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5311 q selected
    | true =>
      simp only [d89791, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5293 q selected
  have h10 (q : Pattern) (selected : d89792 q = 0) : d91013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89792, d91013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89792, d91013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89797 q = 0) : d91018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89797, d91018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5312 q selected
    | true =>
      simp only [d89797, d91018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d89798 q = 0) : d91019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89798, d91019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89798, d91019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89799 q = 0) : d91020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89799, d91020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89799, d91020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89800 q = 0) : d91021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89800, d91021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89800, d91021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d89801 q = 0) : d91022 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89801, d91022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89801, d91022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d89804 q = 0) : d91025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89804, d91025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5314 q selected
    | true =>
      simp only [d89804, d91025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5295 q selected
  have h17 (q : Pattern) (selected : d89805 q = 0) : d91026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89805, d91026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89805, d91026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d89806 q = 0) : d91027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89806, d91027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d89806, d91027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d89807 q = 0) : d91028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89807, d91028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89807, d91028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d89809 q = 0) : d91030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89809, d91030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5315 q selected
    | true =>
      simp only [d89809, d91030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5296 q selected
  have h21 (q : Pattern) (selected : d89810 q = 0) : d91031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89810, d91031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89810, d91031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d89811 q = 0) : d91032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89811, d91032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d89811, d91032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d89813 q = 0) : d91034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89813, d91034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5316 q selected
    | true =>
      simp only [d89813, d91034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5297 q selected
  have h24 (q : Pattern) (selected : d89815 q = 0) : d90940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89815, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5317 q selected
    | true =>
      simp only [d89815, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5298 q selected
  have h25 (q : Pattern) (selected : d89816 q = 0) : d91035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89816, d91035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d89816, d91035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d89818 q = 0) : d91037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89818, d91037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5318 q selected
    | true =>
      simp only [d89818, d91037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d89819 q = 0) : d91038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89819, d91038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d89819, d91038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d89820 q = 0) : d91039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89820, d91039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d89820, d91039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d89821 q = 0) : d91040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89821, d91040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d89821, d91040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d89822 q = 0) : d91041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89822, d91041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d89822, d91041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d89823 q = 0) : d91042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89823, d91042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d89823, d91042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5320 (p : Pattern) (selected : d89825 p = 0) : d91044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89686 q = 0) : d90924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5292 q selected
    | true =>
      simp only [d89686, d90924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
  have h2 (q : Pattern) (selected : d89755 q = 0) : d90981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89755, d90981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89755, d90981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89756 q = 0) : d90982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89756, d90982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89756, d90982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89757 q = 0) : d90983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89757, d90983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89757, d90983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89758 q = 0) : d90984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89758, d90984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89758, d90984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89612 q = 0) : d90850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5280 q selected
    | true =>
      simp only [d89612, d90850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d89655 q = 0) : d90893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89655, d90893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89656 q = 0) : d90894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89656, d90894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89657 q = 0) : d90895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89657, d90895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89658 q = 0) : d90896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89658, d90896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89825 q = 0) : d91044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89825, d91044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89825, d91044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5321 (p : Pattern) (selected : d89832 p = 0) : d91051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89813 q = 0) : d91034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89813, d91034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5316 q selected
    | true =>
      simp only [d89813, d91034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5297 q selected
  have h2 (q : Pattern) (selected : d89815 q = 0) : d90940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89815, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5317 q selected
    | true =>
      simp only [d89815, d90940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5298 q selected
  have h3 (q : Pattern) (selected : d89816 q = 0) : d91035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89816, d91035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89816, d91035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89818 q = 0) : d91037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89818, d91037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5318 q selected
    | true =>
      simp only [d89818, d91037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89819 q = 0) : d91038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89819, d91038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89819, d91038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89820 q = 0) : d91039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89820, d91039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89820, d91039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89830 q = 0) : d91049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89830, d91049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89830, d91049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89831 q = 0) : d91050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89831, d91050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89831, d91050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89832 q = 0) : d91051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89832, d91051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89832, d91051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5322 (p : Pattern) (selected : d89834 p = 0) : d91053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89619 q = 0) : d90857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5282 q selected
    | true =>
      simp only [d89619, d90857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89662 q = 0) : d90900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89662, d90900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89662, d90900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89663 q = 0) : d90901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89663, d90901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89663, d90901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89664 q = 0) : d90902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89664, d90902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89664, d90902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89665 q = 0) : d90903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89665, d90903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89665, d90903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89834 q = 0) : d91053 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89834, d91053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89834, d91053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5323 (p : Pattern) (selected : d89843 p = 0) : d91062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d424 q = 0) : d52190 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d424, d52190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro254 q selected
    | true =>
      simp only [d424, d52190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6773 q = 0) : d81561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4225 q selected
    | true =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89840 q = 0) : d91059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89840, d91059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89840, d91059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89841 q = 0) : d91060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89841, d91060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89841, d91060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89842 q = 0) : d91061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89842, d91061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89842, d91061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89843 q = 0) : d91062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89843, d91062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89843, d91062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5324 (p : Pattern) (selected : d89848 p = 0) : d90963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d443 q = 0) : d52056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d443, d52056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro257 q selected
    | true =>
      simp only [d443, d52056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d257 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro226 q selected
    | true =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89845 q = 0) : d90960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89845, d90960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89845, d90960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89846 q = 0) : d90961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89846, d90961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89846, d90961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89847 q = 0) : d90962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89847, d90962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89847, d90962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89848 q = 0) : d90963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89848, d90963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89848, d90963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5325 (p : Pattern) (selected : d89854 p = 0) : d91068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d238 q = 0) : d52056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro223 q selected
    | true =>
      simp only [d238, d52056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89851 q = 0) : d91065 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89851, d91065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89851, d91065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89852 q = 0) : d91066 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89852, d91066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89852, d91066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89853 q = 0) : d91067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89853, d91067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89853, d91067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89854 q = 0) : d91068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89854, d91068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89854, d91068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5326 (p : Pattern) (selected : d89860 p = 0) : d91074 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89844 q = 0) : d91063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89844, d91063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5323 q selected
    | true =>
      simp only [d89844, d91063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5302 q selected
  have h2 (q : Pattern) (selected : d89849 q = 0) : d90964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89849, d90964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5324 q selected
    | true =>
      simp only [d89849, d90964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5303 q selected
  have h3 (q : Pattern) (selected : d89850 q = 0) : d91064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89850, d91064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89850, d91064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89855 q = 0) : d91069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89855, d91069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5325 q selected
    | true =>
      simp only [d89855, d91069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89856 q = 0) : d91070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89856, d91070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89856, d91070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89857 q = 0) : d91071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89857, d91071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89857, d91071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89858 q = 0) : d91072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89858, d91072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89858, d91072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89859 q = 0) : d91073 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89859, d91073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89859, d91073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89860 q = 0) : d91074 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89860, d91074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89860, d91074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5327 (p : Pattern) (selected : d89866 p = 0) : d91080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89639 q = 0) : d90877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89639, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5285 q selected
    | true =>
      simp only [d89639, d90877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89862 q = 0) : d91076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89862, d91076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89862, d91076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89863 q = 0) : d91077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89863, d91077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89863, d91077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89864 q = 0) : d91078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89864, d91078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89864, d91078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89865 q = 0) : d91079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89865, d91079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89865, d91079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89866 q = 0) : d91080 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89866, d91080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89866, d91080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5328 (p : Pattern) (selected : d89872 p = 0) : d91086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89760 q = 0) : d90986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89760, d90986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89760, d90986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5306 q selected
  have h2 (q : Pattern) (selected : d89761 q = 0) : d90987 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89761, d90987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89761, d90987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89767 q = 0) : d90993 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89767, d90993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5306 q selected
    | true =>
      simp only [d89767, d90993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5307 q selected
  have h4 (q : Pattern) (selected : d89768 q = 0) : d90994 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89768, d90994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89768, d90994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89769 q = 0) : d90995 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89769, d90995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89769, d90995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89824 q = 0) : d91043 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89824, d91043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5313 q selected
    | true =>
      simp only [d89824, d91043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5319 q selected
  have h7 (q : Pattern) (selected : d89826 q = 0) : d91045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89826, d91045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5320 q selected
    | true =>
      simp only [d89826, d91045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5289 q selected
  have h8 (q : Pattern) (selected : d89827 q = 0) : d91046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89827, d91046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89827, d91046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89828 q = 0) : d91047 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89828, d91047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89828, d91047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d89829 q = 0) : d91048 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89829, d91048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89829, d91048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89833 q = 0) : d91052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89833, d91052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89833, d91052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5321 q selected
  have h12 (q : Pattern) (selected : d89835 q = 0) : d91054 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89835, d91054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89835, d91054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5322 q selected
  have h13 (q : Pattern) (selected : d89836 q = 0) : d91055 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89836, d91055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89836, d91055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89837 q = 0) : d91056 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89837, d91056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d89837, d91056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d89838 q = 0) : d91057 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89838, d91057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d89838, d91057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d89839 q = 0) : d91058 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89839, d91058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89839, d91058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d89861 q = 0) : d91075 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89861, d91075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89861, d91075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5326 q selected
  have h18 (q : Pattern) (selected : d89867 q = 0) : d91081 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89867, d91081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89867, d91081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5327 q selected
  have h19 (q : Pattern) (selected : d89868 q = 0) : d91082 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89868, d91082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d89868, d91082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d89869 q = 0) : d91083 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89869, d91083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d89869, d91083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d89870 q = 0) : d91084 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89870, d91084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d89870, d91084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d89871 q = 0) : d91085 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d89871, d91085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d89871, d91085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d89872 q = 0) : d91086 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d89872, d91086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d89872, d91086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5329 (p : Pattern) (selected : d89878 p = 0) : d91092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89651 q = 0) : d90889 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89651, d90889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89651, d90889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5287 q selected
  have h2 (q : Pattern) (selected : d89652 q = 0) : d90890 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89652, d90890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89652, d90890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89653 q = 0) : d90891 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89653, d90891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89653, d90891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89654 q = 0) : d90892 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89654, d90892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89654, d90892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89750 q = 0) : d90976 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89750, d90976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89750, d90976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5305 q selected
  have h6 (q : Pattern) (selected : d89751 q = 0) : d90977 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89751, d90977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89751, d90977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89752 q = 0) : d90978 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89752, d90978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89752, d90978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89753 q = 0) : d90979 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89753, d90979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89753, d90979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89754 q = 0) : d90980 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89754, d90980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89754, d90980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89873 q = 0) : d91087 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d89873, d91087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89873, d91087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5328 q selected
  have h11 (q : Pattern) (selected : d89874 q = 0) : d91088 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d89874, d91088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89874, d91088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d89875 q = 0) : d91089 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d89875, d91089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89875, d91089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d89876 q = 0) : d91090 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d89876, d91090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89876, d91090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89877 q = 0) : d91091 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d89877, d91091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89877, d91091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d89878 q = 0) : d91092 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d89878, d91092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d89878, d91092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro5330 (p : Pattern) (selected : d89882 p = 0) : d91096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89879 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89880 q = 0) : d91094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89881 q = 0) : d91095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89881, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89881, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89882 q = 0) : d91096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89882, d91096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89882, d91096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5331 (p : Pattern) (selected : d89886 p = 0) : d91100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89883 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89884 q = 0) : d91098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89885 q = 0) : d91099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89885, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89885, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89886 q = 0) : d91100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89886, d91100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89886, d91100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5332 (p : Pattern) (selected : d89892 p = 0) : d91106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89887 q = 0) : d91101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89887, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5330 q selected
    | true =>
      simp only [d89887, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5331 q selected
  have h2 (q : Pattern) (selected : d89888 q = 0) : d91102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89888, d91102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89888, d91102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89889 q = 0) : d91103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89889, d91103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89889, d91103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89890 q = 0) : d91104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89890, d91104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89890, d91104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89891 q = 0) : d91105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89891, d91105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89891, d91105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89892 q = 0) : d91106 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89892, d91106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89892, d91106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5333 (p : Pattern) (selected : d89895 p = 0) : d91109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89879 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89880 q = 0) : d91094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89881 q = 0) : d91095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89881, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89881, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89895 q = 0) : d91109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89895, d91109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89895, d91109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5334 (p : Pattern) (selected : d89896 p = 0) : d91110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89883 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89884 q = 0) : d91098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89885 q = 0) : d91099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89885, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89885, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89896 q = 0) : d91110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89896, d91110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89896, d91110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5335 (p : Pattern) (selected : d89902 p = 0) : d91116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89887 q = 0) : d91101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89887, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5330 q selected
    | true =>
      simp only [d89887, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5331 q selected
  have h2 (q : Pattern) (selected : d89888 q = 0) : d91102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89888, d91102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89888, d91102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89889 q = 0) : d91103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89889, d91103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89889, d91103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89890 q = 0) : d91104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89890, d91104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89890, d91104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89891 q = 0) : d91105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89891, d91105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89891, d91105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89897 q = 0) : d91111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89897, d91111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5333 q selected
    | true =>
      simp only [d89897, d91111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5334 q selected
  have h7 (q : Pattern) (selected : d89898 q = 0) : d91112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89898, d91112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89898, d91112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89899 q = 0) : d91113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89899, d91113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89899, d91113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89900 q = 0) : d91114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89900, d91114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89900, d91114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89901 q = 0) : d91115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89901, d91115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89901, d91115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89902 q = 0) : d91116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89902, d91116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89902, d91116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5336 (p : Pattern) (selected : d89907 p = 0) : d91121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89879 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89880 q = 0) : d91094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89906 q = 0) : d91120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89906, d91120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89906, d91120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89907 q = 0) : d91121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89907, d91121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89907, d91121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5337 (p : Pattern) (selected : d89909 p = 0) : d91123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89883 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89884 q = 0) : d91098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89908 q = 0) : d91122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89908, d91122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89908, d91122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89909 q = 0) : d91123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89909, d91123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89909, d91123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5338 (p : Pattern) (selected : d89916 p = 0) : d91130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89879 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89914 q = 0) : d91128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89914, d91128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89914, d91128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89915 q = 0) : d91129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89915, d91129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89915, d91129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89916 q = 0) : d91130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89916, d91130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89916, d91130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5339 (p : Pattern) (selected : d89919 p = 0) : d91133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89883 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89917 q = 0) : d91131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89917, d91131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89917, d91131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89918 q = 0) : d91132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89918, d91132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89918, d91132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89919 q = 0) : d91133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89919, d91133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89919, d91133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5340 (p : Pattern) (selected : d89926 p = 0) : d91140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d555 q = 0) : d52302 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro279 q selected
    | true =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6800 q = 0) : d81588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4230 q selected
    | true =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89923 q = 0) : d91137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89923, d91137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89923, d91137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89924 q = 0) : d91138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89924, d91138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89924, d91138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89925 q = 0) : d91139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89925, d91139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89925, d91139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89926 q = 0) : d91140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89926, d91140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89926, d91140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5341 (p : Pattern) (selected : d89930 p = 0) : d91144 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4825 q = 0) : d68921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2774 q selected
    | true =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89927 q = 0) : d91141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89927, d91141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89927, d91141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89928 q = 0) : d91142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89928, d91142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89928, d91142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89929 q = 0) : d91143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89929, d91143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89929, d91143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89930 q = 0) : d91144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89930, d91144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89930, d91144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5342 (p : Pattern) (selected : d89935 p = 0) : d91096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d587 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d587, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro284 q selected
    | true =>
      simp only [d587, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89932 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89932, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89932, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89933 q = 0) : d91094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89933, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89933, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89934 q = 0) : d91095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89934, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89934, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89935 q = 0) : d91096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89935, d91096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89935, d91096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5343 (p : Pattern) (selected : d89939 p = 0) : d91100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89936 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89936, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89936, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89937 q = 0) : d91098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89937, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89937, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89938 q = 0) : d91099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89938, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89938, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89939 q = 0) : d91100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89939, d91100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89939, d91100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5344 (p : Pattern) (selected : d89945 p = 0) : d91150 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89942 q = 0) : d91147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89942, d91147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89942, d91147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89943 q = 0) : d91148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89943, d91148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89943, d91148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89944 q = 0) : d91149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89944, d91149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89944, d91149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89945 q = 0) : d91150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89945, d91150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89945, d91150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5345 (p : Pattern) (selected : d89951 p = 0) : d91156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89910 q = 0) : d91124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89910, d91124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5336 q selected
    | true =>
      simp only [d89910, d91124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5337 q selected
  have h2 (q : Pattern) (selected : d89911 q = 0) : d91125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89911, d91125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89911, d91125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89912 q = 0) : d91126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89912, d91126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89912, d91126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89913 q = 0) : d91127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89913, d91127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89913, d91127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89920 q = 0) : d91134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89920, d91134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5338 q selected
    | true =>
      simp only [d89920, d91134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5339 q selected
  have h6 (q : Pattern) (selected : d89921 q = 0) : d91135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89921, d91135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89921, d91135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89922 q = 0) : d91136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89922, d91136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89922, d91136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89931 q = 0) : d91145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89931, d91145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5340 q selected
    | true =>
      simp only [d89931, d91145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5341 q selected
  have h9 (q : Pattern) (selected : d89940 q = 0) : d91101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89940, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5342 q selected
    | true =>
      simp only [d89940, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5343 q selected
  have h10 (q : Pattern) (selected : d89941 q = 0) : d91146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89941, d91146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89941, d91146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89946 q = 0) : d91151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89946, d91151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5344 q selected
    | true =>
      simp only [d89946, d91151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d89947 q = 0) : d91152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89947, d91152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89947, d91152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89948 q = 0) : d91153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89948, d91153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89948, d91153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89949 q = 0) : d91154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89949, d91154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89949, d91154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d89950 q = 0) : d91155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89950, d91155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89950, d91155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d89951 q = 0) : d91156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89951, d91156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89951, d91156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5346 (p : Pattern) (selected : d89952 p = 0) : d91157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89879 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89880 q = 0) : d91094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89880, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89906 q = 0) : d91120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89906, d91120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89906, d91120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89952 q = 0) : d91157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89952, d91157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89952, d91157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5347 (p : Pattern) (selected : d89953 p = 0) : d91158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89883 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89884 q = 0) : d91098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89884, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89908 q = 0) : d91122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89908, d91122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89908, d91122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89953 q = 0) : d91158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89953, d91158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89953, d91158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5348 (p : Pattern) (selected : d89958 p = 0) : d91163 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89879 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89879, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89914 q = 0) : d91128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89914, d91128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89914, d91128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89915 q = 0) : d91129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89915, d91129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89915, d91129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89958 q = 0) : d91163 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89958, d91163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89958, d91163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5349 (p : Pattern) (selected : d89959 p = 0) : d91164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89883 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89883, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89917 q = 0) : d91131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89917, d91131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89917, d91131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89918 q = 0) : d91132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89918, d91132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89918, d91132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89959 q = 0) : d91164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89959, d91164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89959, d91164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5350 (p : Pattern) (selected : d89963 p = 0) : d91168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d555 q = 0) : d52302 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro279 q selected
    | true =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6800 q = 0) : d81588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4230 q selected
    | true =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89923 q = 0) : d91137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89923, d91137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89923, d91137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89924 q = 0) : d91138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89924, d91138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89924, d91138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89925 q = 0) : d91139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89925, d91139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89925, d91139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89963 q = 0) : d91168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89963, d91168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89963, d91168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5351 (p : Pattern) (selected : d89964 p = 0) : d91169 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4825 q = 0) : d68921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2774 q selected
    | true =>
      simp only [d4825, d68921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89927 q = 0) : d91141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89927, d91141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89927, d91141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89928 q = 0) : d91142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89928, d91142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89928, d91142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89929 q = 0) : d91143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89929, d91143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89929, d91143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89964 q = 0) : d91169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89964, d91169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89964, d91169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5352 (p : Pattern) (selected : d89966 p = 0) : d91109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d587 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d587, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro284 q selected
    | true =>
      simp only [d587, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89932 q = 0) : d91093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89932, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89932, d91093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89933 q = 0) : d91094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89933, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89933, d91094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89934 q = 0) : d91095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89934, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89934, d91095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89966 q = 0) : d91109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89966, d91109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89966, d91109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5353 (p : Pattern) (selected : d89967 p = 0) : d91110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89936 q = 0) : d91097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89936, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89936, d91097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89937 q = 0) : d91098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89937, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89937, d91098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89938 q = 0) : d91099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89938, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89938, d91099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89967 q = 0) : d91110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89967, d91110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89967, d91110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5354 (p : Pattern) (selected : d89970 p = 0) : d91172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89942 q = 0) : d91147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d89942, d91147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89942, d91147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89943 q = 0) : d91148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d89943, d91148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89943, d91148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89944 q = 0) : d91149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d89944, d91149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89944, d91149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89970 q = 0) : d91172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d89970, d91172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89970, d91172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5355 (p : Pattern) (selected : d89976 p = 0) : d91178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89910 q = 0) : d91124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89910, d91124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5336 q selected
    | true =>
      simp only [d89910, d91124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5337 q selected
  have h2 (q : Pattern) (selected : d89911 q = 0) : d91125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89911, d91125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89911, d91125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89912 q = 0) : d91126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89912, d91126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89912, d91126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89913 q = 0) : d91127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89913, d91127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89913, d91127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89920 q = 0) : d91134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89920, d91134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5338 q selected
    | true =>
      simp only [d89920, d91134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5339 q selected
  have h6 (q : Pattern) (selected : d89921 q = 0) : d91135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89921, d91135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89921, d91135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89922 q = 0) : d91136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89922, d91136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89922, d91136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d89931 q = 0) : d91145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89931, d91145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5340 q selected
    | true =>
      simp only [d89931, d91145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5341 q selected
  have h9 (q : Pattern) (selected : d89940 q = 0) : d91101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89940, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5342 q selected
    | true =>
      simp only [d89940, d91101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5343 q selected
  have h10 (q : Pattern) (selected : d89941 q = 0) : d91146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89941, d91146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89941, d91146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89946 q = 0) : d91151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89946, d91151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5344 q selected
    | true =>
      simp only [d89946, d91151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d89947 q = 0) : d91152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89947, d91152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d89947, d91152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d89948 q = 0) : d91153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89948, d91153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d89948, d91153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d89949 q = 0) : d91154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89949, d91154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89949, d91154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d89950 q = 0) : d91155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89950, d91155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89950, d91155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d89954 q = 0) : d91159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89954, d91159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5346 q selected
    | true =>
      simp only [d89954, d91159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5347 q selected
  have h17 (q : Pattern) (selected : d89955 q = 0) : d91160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89955, d91160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89955, d91160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d89956 q = 0) : d91161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89956, d91161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d89956, d91161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d89957 q = 0) : d91162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89957, d91162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89957, d91162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d89960 q = 0) : d91165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89960, d91165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5348 q selected
    | true =>
      simp only [d89960, d91165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5349 q selected
  have h21 (q : Pattern) (selected : d89961 q = 0) : d91166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89961, d91166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89961, d91166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d89962 q = 0) : d91167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89962, d91167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d89962, d91167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d89965 q = 0) : d91170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89965, d91170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5350 q selected
    | true =>
      simp only [d89965, d91170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5351 q selected
  have h24 (q : Pattern) (selected : d89968 q = 0) : d91111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89968, d91111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5352 q selected
    | true =>
      simp only [d89968, d91111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5353 q selected
  have h25 (q : Pattern) (selected : d89969 q = 0) : d91171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89969, d91171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d89969, d91171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d89971 q = 0) : d91173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89971, d91173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5354 q selected
    | true =>
      simp only [d89971, d91173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d89972 q = 0) : d91174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89972, d91174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d89972, d91174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d89973 q = 0) : d91175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89973, d91175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d89973, d91175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d89974 q = 0) : d91176 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89974, d91176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d89974, d91176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d89975 q = 0) : d91177 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89975, d91177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d89975, d91177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d89976 q = 0) : d91178 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89976, d91178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d89976, d91178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5356 (p : Pattern) (selected : d89988 p = 0) : d91190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89978 q = 0) : d91180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89978, d91180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5341 q selected
    | true =>
      simp only [d89978, d91180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5331 q selected
  have h2 (q : Pattern) (selected : d89979 q = 0) : d91181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89979, d91181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89979, d91181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89980 q = 0) : d91182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89980, d91182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89980, d91182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89981 q = 0) : d91183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89981, d91183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89981, d91183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89982 q = 0) : d91184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89982, d91184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89982, d91184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89983 q = 0) : d91185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89983, d91185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5331 q selected
    | true =>
      simp only [d89983, d91185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d89984 q = 0) : d91186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89984, d91186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89984, d91186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89985 q = 0) : d91187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89985, d91187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89985, d91187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89986 q = 0) : d91188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89986, d91188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89986, d91188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89987 q = 0) : d91189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89987, d91189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89987, d91189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89988 q = 0) : d91190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89988, d91190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89988, d91190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5357 (p : Pattern) (selected : d89994 p = 0) : d91196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89983 q = 0) : d91185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89983, d91185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5331 q selected
    | true =>
      simp only [d89983, d91185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89984 q = 0) : d91186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89984, d91186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89984, d91186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89985 q = 0) : d91187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89985, d91187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89985, d91187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89986 q = 0) : d91188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89986, d91188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89986, d91188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89987 q = 0) : d91189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89987, d91189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89987, d91189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89989 q = 0) : d91191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89989, d91191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5334 q selected
    | true =>
      simp only [d89989, d91191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d89990 q = 0) : d91192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89990, d91192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89990, d91192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d89991 q = 0) : d91193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89991, d91193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d89991, d91193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d89992 q = 0) : d91194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89992, d91194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89992, d91194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d89993 q = 0) : d91195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89993, d91195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89993, d91195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d89994 q = 0) : d91196 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89994, d91196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89994, d91196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5358 (p : Pattern) (selected : d90001 p = 0) : d91203 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89965 q = 0) : d91170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89965, d91170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5350 q selected
    | true =>
      simp only [d89965, d91170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5351 q selected
  have h2 (q : Pattern) (selected : d89968 q = 0) : d91111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89968, d91111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5352 q selected
    | true =>
      simp only [d89968, d91111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5353 q selected
  have h3 (q : Pattern) (selected : d89969 q = 0) : d91171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89969, d91171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89969, d91171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d89971 q = 0) : d91173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89971, d91173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5354 q selected
    | true =>
      simp only [d89971, d91173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89972 q = 0) : d91174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89972, d91174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d89972, d91174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d89973 q = 0) : d91175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89973, d91175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89973, d91175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d89999 q = 0) : d91201 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89999, d91201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89999, d91201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90000 q = 0) : d91202 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90000, d91202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90000, d91202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90001 q = 0) : d91203 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90001, d91203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90001, d91203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5359 (p : Pattern) (selected : d90003 p = 0) : d91205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89989 q = 0) : d91191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d89989, d91191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5334 q selected
    | true =>
      simp only [d89989, d91191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d89990 q = 0) : d91192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d89990, d91192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89990, d91192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d89991 q = 0) : d91193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d89991, d91193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89991, d91193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d89992 q = 0) : d91194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d89992, d91194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89992, d91194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d89993 q = 0) : d91195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d89993, d91195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89993, d91195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90003 q = 0) : d91205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90003, d91205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90003, d91205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5360 (p : Pattern) (selected : d90012 p = 0) : d91214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d671 q = 0) : d52375 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d52375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro302 q selected
    | true =>
      simp only [d671, d52375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6846 q = 0) : d81634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d81634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4239 q selected
    | true =>
      simp only [d6846, d81634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90009 q = 0) : d91211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90009, d91211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90009, d91211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90010 q = 0) : d91212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90010, d91212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90010, d91212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90011 q = 0) : d91213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90011, d91213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90011, d91213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90012 q = 0) : d91214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90012, d91214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90012, d91214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5361 (p : Pattern) (selected : d90016 p = 0) : d91218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6085 q = 0) : d75847 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6085, d75847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3610 q selected
    | true =>
      simp only [d6085, d75847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d684 q = 0) : d52388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro305 q selected
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90013 q = 0) : d91215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90013, d91215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90013, d91215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90014 q = 0) : d91216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90014, d91216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90014, d91216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90015 q = 0) : d91217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90015, d91217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90015, d91217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90016 q = 0) : d91218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90016, d91218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90016, d91218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5362 (p : Pattern) (selected : d90021 p = 0) : d91223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d704 q = 0) : d52380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d704, d52380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro308 q selected
    | true =>
      simp only [d704, d52380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d708 q = 0) : d52388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d708, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro309 q selected
    | true =>
      simp only [d708, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90018 q = 0) : d91220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90018, d91220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90018, d91220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90019 q = 0) : d91221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90019, d91221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90019, d91221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90020 q = 0) : d91222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90020, d91222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90020, d91222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90021 q = 0) : d91223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90021, d91223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90021, d91223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5363 (p : Pattern) (selected : d90025 p = 0) : d91227 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d708 q = 0) : d52388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d708, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro309 q selected
    | true =>
      simp only [d708, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90022 q = 0) : d91224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90022, d91224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90022, d91224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90023 q = 0) : d91225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90023, d91225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90023, d91225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90024 q = 0) : d91226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90024, d91226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90024, d91226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90025 q = 0) : d91227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90025, d91227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90025, d91227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5364 (p : Pattern) (selected : d90031 p = 0) : d91233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d676 q = 0) : d52380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d52380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro303 q selected
    | true =>
      simp only [d676, d52380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90028 q = 0) : d91230 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90028, d91230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90028, d91230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90029 q = 0) : d91231 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90029, d91231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90029, d91231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90030 q = 0) : d91232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90030, d91232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90030, d91232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90031 q = 0) : d91233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90031, d91233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90031, d91233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5365 (p : Pattern) (selected : d90037 p = 0) : d91239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90017 q = 0) : d91219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90017, d91219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5360 q selected
    | true =>
      simp only [d90017, d91219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5361 q selected
  have h2 (q : Pattern) (selected : d90026 q = 0) : d91228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90026, d91228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5362 q selected
    | true =>
      simp only [d90026, d91228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5363 q selected
  have h3 (q : Pattern) (selected : d90027 q = 0) : d91229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90027, d91229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90027, d91229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90032 q = 0) : d91234 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90032, d91234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5364 q selected
    | true =>
      simp only [d90032, d91234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90033 q = 0) : d91235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90033, d91235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90033, d91235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90034 q = 0) : d91236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90034, d91236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90034, d91236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90035 q = 0) : d91237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90035, d91237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90035, d91237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90036 q = 0) : d91238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90036, d91238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90036, d91238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90037 q = 0) : d91239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90037, d91239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90037, d91239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5366 (p : Pattern) (selected : d90042 p = 0) : d91227 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d684 q = 0) : d52388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro305 q selected
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90039 q = 0) : d91224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90039, d91224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90039, d91224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90040 q = 0) : d91225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90040, d91225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90040, d91225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90041 q = 0) : d91226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90041, d91226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90041, d91226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90042 q = 0) : d91227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90042, d91227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90042, d91227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5367 (p : Pattern) (selected : d90048 p = 0) : d91246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90043 q = 0) : d91241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90043, d91241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5366 q selected
    | true =>
      simp only [d90043, d91241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90044 q = 0) : d91242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90044, d91242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90044, d91242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90045 q = 0) : d91243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90045, d91243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90045, d91243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90046 q = 0) : d91244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90046, d91244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90046, d91244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90047 q = 0) : d91245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90047, d91245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90047, d91245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90048 q = 0) : d91246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90048, d91246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90048, d91246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5368 (p : Pattern) (selected : d90054 p = 0) : d91252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d89893 q = 0) : d91107 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89893, d91107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d89893, d91107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5332 q selected
  have h2 (q : Pattern) (selected : d89894 q = 0) : d91108 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89894, d91108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d89894, d91108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d89903 q = 0) : d91117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89903, d91117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5332 q selected
    | true =>
      simp only [d89903, d91117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5335 q selected
  have h4 (q : Pattern) (selected : d89904 q = 0) : d91118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89904, d91118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d89904, d91118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d89905 q = 0) : d91119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89905, d91119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d89905, d91119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d89977 q = 0) : d91179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89977, d91179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5345 q selected
    | true =>
      simp only [d89977, d91179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5355 q selected
  have h7 (q : Pattern) (selected : d89995 q = 0) : d91197 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d89995, d91197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5356 q selected
    | true =>
      simp only [d89995, d91197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5357 q selected
  have h8 (q : Pattern) (selected : d89996 q = 0) : d91198 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d89996, d91198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d89996, d91198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d89997 q = 0) : d91199 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d89997, d91199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d89997, d91199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d89998 q = 0) : d91200 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d89998, d91200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d89998, d91200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90002 q = 0) : d91204 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90002, d91204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90002, d91204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5358 q selected
  have h12 (q : Pattern) (selected : d90004 q = 0) : d91206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90004, d91206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90004, d91206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5359 q selected
  have h13 (q : Pattern) (selected : d90005 q = 0) : d91207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90005, d91207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90005, d91207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90006 q = 0) : d91208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90006, d91208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d90006, d91208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d90007 q = 0) : d91209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90007, d91209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d90007, d91209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d90008 q = 0) : d91210 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90008, d91210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90008, d91210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d90038 q = 0) : d91240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90038, d91240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90038, d91240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5365 q selected
  have h18 (q : Pattern) (selected : d90049 q = 0) : d91247 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90049, d91247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90049, d91247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5367 q selected
  have h19 (q : Pattern) (selected : d90050 q = 0) : d91248 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90050, d91248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d90050, d91248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d90051 q = 0) : d91249 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90051, d91249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d90051, d91249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d90052 q = 0) : d91250 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90052, d91250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d90052, d91250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d90053 q = 0) : d91251 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90053, d91251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d90053, d91251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d90054 q = 0) : d91252 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d90054, d91252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d90054, d91252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5369 (p : Pattern) (selected : d90060 p = 0) : d91258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90055 q = 0) : d91253 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d90055, d91253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90055, d91253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5368 q selected
  have h2 (q : Pattern) (selected : d90056 q = 0) : d91254 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d90056, d91254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90056, d91254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90057 q = 0) : d91255 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d90057, d91255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90057, d91255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90058 q = 0) : d91256 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d90058, d91256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90058, d91256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90059 q = 0) : d91257 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d90059, d91257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90059, d91257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90060 q = 0) : d91258 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d90060, d91258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90060, d91258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5370 (p : Pattern) (selected : d90065 p = 0) : d91263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90062 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90063 q = 0) : d91261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90064 q = 0) : d91262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90064, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90064, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90065 q = 0) : d91263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90065, d91263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90065, d91263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5371 (p : Pattern) (selected : d90069 p = 0) : d91267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90066 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90067 q = 0) : d91265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90068 q = 0) : d91266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90068, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90068, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90069 q = 0) : d91267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90069, d91267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90069, d91267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5372 (p : Pattern) (selected : d90075 p = 0) : d91273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90070 q = 0) : d91268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90070, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5370 q selected
    | true =>
      simp only [d90070, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5371 q selected
  have h2 (q : Pattern) (selected : d90071 q = 0) : d91269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90071, d91269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90071, d91269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90072 q = 0) : d91270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90072, d91270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90072, d91270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90073 q = 0) : d91271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90073, d91271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90073, d91271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90074 q = 0) : d91272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90074, d91272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90074, d91272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90075 q = 0) : d91273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90075, d91273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90075, d91273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5373 (p : Pattern) (selected : d90078 p = 0) : d91276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90062 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90063 q = 0) : d91261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90064 q = 0) : d91262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90064, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90064, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90078 q = 0) : d91276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90078, d91276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90078, d91276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5374 (p : Pattern) (selected : d90079 p = 0) : d91277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90066 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90067 q = 0) : d91265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90068 q = 0) : d91266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90068, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90068, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90079 q = 0) : d91277 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90079, d91277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90079, d91277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5375 (p : Pattern) (selected : d90085 p = 0) : d91283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90070 q = 0) : d91268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90070, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5370 q selected
    | true =>
      simp only [d90070, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5371 q selected
  have h2 (q : Pattern) (selected : d90071 q = 0) : d91269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90071, d91269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90071, d91269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90072 q = 0) : d91270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90072, d91270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90072, d91270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90073 q = 0) : d91271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90073, d91271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90073, d91271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90074 q = 0) : d91272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90074, d91272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90074, d91272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90080 q = 0) : d91278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90080, d91278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5373 q selected
    | true =>
      simp only [d90080, d91278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5374 q selected
  have h7 (q : Pattern) (selected : d90081 q = 0) : d91279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90081, d91279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90081, d91279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90082 q = 0) : d91280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90082, d91280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90082, d91280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90083 q = 0) : d91281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90083, d91281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90083, d91281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90084 q = 0) : d91282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90084, d91282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90084, d91282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90085 q = 0) : d91283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90085, d91283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90085, d91283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5376 (p : Pattern) (selected : d90090 p = 0) : d91288 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90062 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90063 q = 0) : d91261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90089 q = 0) : d91287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90089, d91287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90089, d91287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90090 q = 0) : d91288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90090, d91288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90090, d91288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5377 (p : Pattern) (selected : d90092 p = 0) : d91290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90066 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90067 q = 0) : d91265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90091 q = 0) : d91289 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90091, d91289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90091, d91289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90092 q = 0) : d91290 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90092, d91290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90092, d91290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5378 (p : Pattern) (selected : d90099 p = 0) : d91297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90062 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90097 q = 0) : d91295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90097, d91295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90097, d91295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90098 q = 0) : d91296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90098, d91296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90098, d91296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90099 q = 0) : d91297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90099, d91297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90099, d91297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5379 (p : Pattern) (selected : d90102 p = 0) : d91300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90066 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90100 q = 0) : d91298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90100, d91298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90100, d91298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90101 q = 0) : d91299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90101, d91299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90101, d91299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90102 q = 0) : d91300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90102, d91300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90102, d91300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5380 (p : Pattern) (selected : d90109 p = 0) : d91307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d846 q = 0) : d52523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro337 q selected
    | true =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6878 q = 0) : d81666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4245 q selected
    | true =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90106 q = 0) : d91304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90106, d91304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90106, d91304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90107 q = 0) : d91305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90107, d91305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90107, d91305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90108 q = 0) : d91306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90108, d91306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90108, d91306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90109 q = 0) : d91307 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90109, d91307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90109, d91307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5381 (p : Pattern) (selected : d90113 p = 0) : d91311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4920 q = 0) : d69013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2786 q selected
    | true =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90110 q = 0) : d91308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90110, d91308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90110, d91308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90111 q = 0) : d91309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90111, d91309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90111, d91309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90112 q = 0) : d91310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90112, d91310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90112, d91310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90113 q = 0) : d91311 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90113, d91311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90113, d91311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5382 (p : Pattern) (selected : d90118 p = 0) : d91263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d893 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d893, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro346 q selected
    | true =>
      simp only [d893, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90115 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90115, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90115, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90116 q = 0) : d91261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90116, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90116, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90117 q = 0) : d91262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90117, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90117, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90118 q = 0) : d91263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90118, d91263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90118, d91263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5383 (p : Pattern) (selected : d90122 p = 0) : d91267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90119 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90119, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90119, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90120 q = 0) : d91265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90120, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90120, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90121 q = 0) : d91266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90121, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90121, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90122 q = 0) : d91267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90122, d91267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90122, d91267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5384 (p : Pattern) (selected : d90128 p = 0) : d91317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90125 q = 0) : d91314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90125, d91314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90125, d91314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90126 q = 0) : d91315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90126, d91315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90126, d91315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90127 q = 0) : d91316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90127, d91316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90127, d91316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90128 q = 0) : d91317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90128, d91317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90128, d91317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5385 (p : Pattern) (selected : d90134 p = 0) : d91323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90093 q = 0) : d91291 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90093, d91291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5376 q selected
    | true =>
      simp only [d90093, d91291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5377 q selected
  have h2 (q : Pattern) (selected : d90094 q = 0) : d91292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90094, d91292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90094, d91292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90095 q = 0) : d91293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90095, d91293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90095, d91293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90096 q = 0) : d91294 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90096, d91294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90096, d91294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90103 q = 0) : d91301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90103, d91301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5378 q selected
    | true =>
      simp only [d90103, d91301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5379 q selected
  have h6 (q : Pattern) (selected : d90104 q = 0) : d91302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90104, d91302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90104, d91302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90105 q = 0) : d91303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90105, d91303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90105, d91303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d90114 q = 0) : d91312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90114, d91312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5380 q selected
    | true =>
      simp only [d90114, d91312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5381 q selected
  have h9 (q : Pattern) (selected : d90123 q = 0) : d91268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90123, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5382 q selected
    | true =>
      simp only [d90123, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5383 q selected
  have h10 (q : Pattern) (selected : d90124 q = 0) : d91313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90124, d91313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90124, d91313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90129 q = 0) : d91318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90129, d91318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5384 q selected
    | true =>
      simp only [d90129, d91318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d90130 q = 0) : d91319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90130, d91319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90130, d91319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d90131 q = 0) : d91320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90131, d91320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90131, d91320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90132 q = 0) : d91321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90132, d91321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90132, d91321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d90133 q = 0) : d91322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90133, d91322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90133, d91322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d90134 q = 0) : d91323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90134, d91323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90134, d91323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5386 (p : Pattern) (selected : d90135 p = 0) : d91324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90062 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90063 q = 0) : d91261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90063, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90089 q = 0) : d91287 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90089, d91287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90089, d91287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90135 q = 0) : d91324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90135, d91324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90135, d91324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5387 (p : Pattern) (selected : d90136 p = 0) : d91325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90066 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90067 q = 0) : d91265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90067, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90091 q = 0) : d91289 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90091, d91289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90091, d91289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90136 q = 0) : d91325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90136, d91325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90136, d91325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5388 (p : Pattern) (selected : d90141 p = 0) : d91330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90062 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90062, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90097 q = 0) : d91295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90097, d91295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90097, d91295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90098 q = 0) : d91296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90098, d91296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90098, d91296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90141 q = 0) : d91330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90141, d91330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90141, d91330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5389 (p : Pattern) (selected : d90142 p = 0) : d91331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90066 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90066, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90100 q = 0) : d91298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90100, d91298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90100, d91298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90101 q = 0) : d91299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90101, d91299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90101, d91299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90142 q = 0) : d91331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90142, d91331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90142, d91331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5390 (p : Pattern) (selected : d90146 p = 0) : d91335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d846 q = 0) : d52523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro337 q selected
    | true =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6878 q = 0) : d81666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4245 q selected
    | true =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90106 q = 0) : d91304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90106, d91304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90106, d91304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90107 q = 0) : d91305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90107, d91305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90107, d91305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90108 q = 0) : d91306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90108, d91306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90108, d91306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90146 q = 0) : d91335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90146, d91335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90146, d91335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5391 (p : Pattern) (selected : d90147 p = 0) : d91336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d4920 q = 0) : d69013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2786 q selected
    | true =>
      simp only [d4920, d69013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90110 q = 0) : d91308 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90110, d91308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90110, d91308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90111 q = 0) : d91309 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90111, d91309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90111, d91309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90112 q = 0) : d91310 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90112, d91310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90112, d91310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90147 q = 0) : d91336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90147, d91336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90147, d91336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5392 (p : Pattern) (selected : d90149 p = 0) : d91276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d893 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d893, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro346 q selected
    | true =>
      simp only [d893, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90115 q = 0) : d91260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90115, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90115, d91260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90116 q = 0) : d91261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90116, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90116, d91261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90117 q = 0) : d91262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90117, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90117, d91262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90149 q = 0) : d91276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90149, d91276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90149, d91276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5393 (p : Pattern) (selected : d90150 p = 0) : d91277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90119 q = 0) : d91264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90119, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90119, d91264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90120 q = 0) : d91265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90120, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90120, d91265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90121 q = 0) : d91266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90121, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90121, d91266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90150 q = 0) : d91277 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90150, d91277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90150, d91277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5394 (p : Pattern) (selected : d90153 p = 0) : d91339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90125 q = 0) : d91314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90125, d91314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90125, d91314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90126 q = 0) : d91315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90126, d91315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90126, d91315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90127 q = 0) : d91316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90127, d91316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90127, d91316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90153 q = 0) : d91339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90153, d91339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90153, d91339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5395 (p : Pattern) (selected : d90159 p = 0) : d91345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90093 q = 0) : d91291 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90093, d91291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5376 q selected
    | true =>
      simp only [d90093, d91291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5377 q selected
  have h2 (q : Pattern) (selected : d90094 q = 0) : d91292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90094, d91292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90094, d91292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90095 q = 0) : d91293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90095, d91293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90095, d91293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90096 q = 0) : d91294 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90096, d91294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90096, d91294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90103 q = 0) : d91301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90103, d91301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5378 q selected
    | true =>
      simp only [d90103, d91301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5379 q selected
  have h6 (q : Pattern) (selected : d90104 q = 0) : d91302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90104, d91302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90104, d91302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90105 q = 0) : d91303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90105, d91303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90105, d91303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d90114 q = 0) : d91312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90114, d91312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5380 q selected
    | true =>
      simp only [d90114, d91312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5381 q selected
  have h9 (q : Pattern) (selected : d90123 q = 0) : d91268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90123, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5382 q selected
    | true =>
      simp only [d90123, d91268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5383 q selected
  have h10 (q : Pattern) (selected : d90124 q = 0) : d91313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90124, d91313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90124, d91313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90129 q = 0) : d91318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90129, d91318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5384 q selected
    | true =>
      simp only [d90129, d91318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d90130 q = 0) : d91319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90130, d91319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90130, d91319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d90131 q = 0) : d91320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90131, d91320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90131, d91320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90132 q = 0) : d91321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90132, d91321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90132, d91321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d90133 q = 0) : d91322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90133, d91322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90133, d91322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d90137 q = 0) : d91326 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90137, d91326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5386 q selected
    | true =>
      simp only [d90137, d91326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5387 q selected
  have h17 (q : Pattern) (selected : d90138 q = 0) : d91327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90138, d91327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90138, d91327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d90139 q = 0) : d91328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90139, d91328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d90139, d91328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d90140 q = 0) : d91329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90140, d91329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90140, d91329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d90143 q = 0) : d91332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90143, d91332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5388 q selected
    | true =>
      simp only [d90143, d91332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5389 q selected
  have h21 (q : Pattern) (selected : d90144 q = 0) : d91333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90144, d91333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90144, d91333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d90145 q = 0) : d91334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90145, d91334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d90145, d91334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d90148 q = 0) : d91337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90148, d91337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5390 q selected
    | true =>
      simp only [d90148, d91337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5391 q selected
  have h24 (q : Pattern) (selected : d90151 q = 0) : d91278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90151, d91278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5392 q selected
    | true =>
      simp only [d90151, d91278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5393 q selected
  have h25 (q : Pattern) (selected : d90152 q = 0) : d91338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90152, d91338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d90152, d91338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d90154 q = 0) : d91340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90154, d91340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5394 q selected
    | true =>
      simp only [d90154, d91340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d90155 q = 0) : d91341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90155, d91341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d90155, d91341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d90156 q = 0) : d91342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90156, d91342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d90156, d91342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d90157 q = 0) : d91343 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90157, d91343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d90157, d91343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d90158 q = 0) : d91344 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90158, d91344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d90158, d91344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d90159 q = 0) : d91345 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90159, d91345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d90159, d91345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5396 (p : Pattern) (selected : d90171 p = 0) : d91357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90161 q = 0) : d91347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90161, d91347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5381 q selected
    | true =>
      simp only [d90161, d91347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5371 q selected
  have h2 (q : Pattern) (selected : d90162 q = 0) : d91348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90162, d91348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90162, d91348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90163 q = 0) : d91349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90163, d91349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90163, d91349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90164 q = 0) : d91350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90164, d91350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90164, d91350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90165 q = 0) : d91351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90165, d91351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90165, d91351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90166 q = 0) : d91352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90166, d91352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5371 q selected
    | true =>
      simp only [d90166, d91352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d90167 q = 0) : d91353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90167, d91353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90167, d91353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90168 q = 0) : d91354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90168, d91354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90168, d91354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90169 q = 0) : d91355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90169, d91355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90169, d91355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90170 q = 0) : d91356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90170, d91356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90170, d91356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90171 q = 0) : d91357 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90171, d91357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90171, d91357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5397 (p : Pattern) (selected : d90177 p = 0) : d91363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90166 q = 0) : d91352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90166, d91352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5371 q selected
    | true =>
      simp only [d90166, d91352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90167 q = 0) : d91353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90167, d91353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90167, d91353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90168 q = 0) : d91354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90168, d91354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90168, d91354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90169 q = 0) : d91355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90169, d91355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90169, d91355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90170 q = 0) : d91356 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90170, d91356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90170, d91356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90172 q = 0) : d91358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90172, d91358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5374 q selected
    | true =>
      simp only [d90172, d91358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d90173 q = 0) : d91359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90173, d91359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90173, d91359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90174 q = 0) : d91360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90174, d91360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90174, d91360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90175 q = 0) : d91361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90175, d91361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90175, d91361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90176 q = 0) : d91362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90176, d91362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90176, d91362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90177 q = 0) : d91363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90177, d91363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90177, d91363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5398 (p : Pattern) (selected : d90184 p = 0) : d91370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90148 q = 0) : d91337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90148, d91337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5390 q selected
    | true =>
      simp only [d90148, d91337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5391 q selected
  have h2 (q : Pattern) (selected : d90151 q = 0) : d91278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90151, d91278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5392 q selected
    | true =>
      simp only [d90151, d91278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5393 q selected
  have h3 (q : Pattern) (selected : d90152 q = 0) : d91338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90152, d91338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90152, d91338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90154 q = 0) : d91340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90154, d91340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5394 q selected
    | true =>
      simp only [d90154, d91340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90155 q = 0) : d91341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90155, d91341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90155, d91341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90156 q = 0) : d91342 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90156, d91342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90156, d91342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90182 q = 0) : d91368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90182, d91368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90182, d91368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90183 q = 0) : d91369 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90183, d91369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90183, d91369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90184 q = 0) : d91370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90184, d91370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90184, d91370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5399 (p : Pattern) (selected : d90186 p = 0) : d91372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90172 q = 0) : d91358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90172, d91358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5374 q selected
    | true =>
      simp only [d90172, d91358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90173 q = 0) : d91359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90173, d91359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90173, d91359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90174 q = 0) : d91360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90174, d91360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90174, d91360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90175 q = 0) : d91361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90175, d91361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90175, d91361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90176 q = 0) : d91362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90176, d91362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90176, d91362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90186 q = 0) : d91372 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90186, d91372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90186, d91372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5400 (p : Pattern) (selected : d90195 p = 0) : d91381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d993 q = 0) : d52612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d52612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro367 q selected
    | true =>
      simp only [d993, d52612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6924 q = 0) : d81712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d81712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4254 q selected
    | true =>
      simp only [d6924, d81712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90192 q = 0) : d91378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90192, d91378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90192, d91378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90193 q = 0) : d91379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90193, d91379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90193, d91379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90194 q = 0) : d91380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90194, d91380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90194, d91380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90195 q = 0) : d91381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90195, d91381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90195, d91381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5401 (p : Pattern) (selected : d90199 p = 0) : d91385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6217 q = 0) : d75968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d75968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3635 q selected
    | true =>
      simp only [d6217, d75968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1006 q = 0) : d52625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro370 q selected
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90196 q = 0) : d91382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90196, d91382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90196, d91382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90197 q = 0) : d91383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90197, d91383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90197, d91383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90198 q = 0) : d91384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90198, d91384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90198, d91384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90199 q = 0) : d91385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90199, d91385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90199, d91385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5402 (p : Pattern) (selected : d90204 p = 0) : d91390 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1037 q = 0) : d52617 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1037, d52617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro375 q selected
    | true =>
      simp only [d1037, d52617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1041 q = 0) : d52625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1041, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro376 q selected
    | true =>
      simp only [d1041, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90201 q = 0) : d91387 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90201, d91387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90201, d91387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90202 q = 0) : d91388 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90202, d91388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90202, d91388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90203 q = 0) : d91389 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90203, d91389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90203, d91389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90204 q = 0) : d91390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90204, d91390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90204, d91390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5403 (p : Pattern) (selected : d90208 p = 0) : d91394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1041 q = 0) : d52625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1041, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro376 q selected
    | true =>
      simp only [d1041, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90205 q = 0) : d91391 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90205, d91391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90205, d91391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90206 q = 0) : d91392 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90206, d91392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90206, d91392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90207 q = 0) : d91393 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90207, d91393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90207, d91393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90208 q = 0) : d91394 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90208, d91394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90208, d91394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5404 (p : Pattern) (selected : d90214 p = 0) : d91400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d998 q = 0) : d52617 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d52617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro368 q selected
    | true =>
      simp only [d998, d52617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90211 q = 0) : d91397 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90211, d91397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90211, d91397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90212 q = 0) : d91398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90212, d91398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90212, d91398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90213 q = 0) : d91399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90213, d91399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90213, d91399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90214 q = 0) : d91400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90214, d91400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90214, d91400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5405 (p : Pattern) (selected : d90220 p = 0) : d91406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90200 q = 0) : d91386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90200, d91386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5400 q selected
    | true =>
      simp only [d90200, d91386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5401 q selected
  have h2 (q : Pattern) (selected : d90209 q = 0) : d91395 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90209, d91395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5402 q selected
    | true =>
      simp only [d90209, d91395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5403 q selected
  have h3 (q : Pattern) (selected : d90210 q = 0) : d91396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90210, d91396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90210, d91396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90215 q = 0) : d91401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90215, d91401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5404 q selected
    | true =>
      simp only [d90215, d91401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90216 q = 0) : d91402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90216, d91402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90216, d91402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90217 q = 0) : d91403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90217, d91403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90217, d91403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90218 q = 0) : d91404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90218, d91404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90218, d91404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90219 q = 0) : d91405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90219, d91405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90219, d91405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90220 q = 0) : d91406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90220, d91406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90220, d91406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5406 (p : Pattern) (selected : d90225 p = 0) : d91394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1006 q = 0) : d52625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro370 q selected
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90222 q = 0) : d91391 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90222, d91391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90222, d91391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90223 q = 0) : d91392 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90223, d91392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90223, d91392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90224 q = 0) : d91393 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90224, d91393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90224, d91393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90225 q = 0) : d91394 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90225, d91394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90225, d91394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5407 (p : Pattern) (selected : d90231 p = 0) : d91413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90226 q = 0) : d91408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90226, d91408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5406 q selected
    | true =>
      simp only [d90226, d91408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90227 q = 0) : d91409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90227, d91409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90227, d91409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90228 q = 0) : d91410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90228, d91410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90228, d91410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90229 q = 0) : d91411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90229, d91411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90229, d91411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90230 q = 0) : d91412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90230, d91412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90230, d91412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90231 q = 0) : d91413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90231, d91413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90231, d91413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5408 (p : Pattern) (selected : d90237 p = 0) : d91419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90076 q = 0) : d91274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90076, d91274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90076, d91274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5372 q selected
  have h2 (q : Pattern) (selected : d90077 q = 0) : d91275 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90077, d91275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90077, d91275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90086 q = 0) : d91284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90086, d91284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5372 q selected
    | true =>
      simp only [d90086, d91284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5375 q selected
  have h4 (q : Pattern) (selected : d90087 q = 0) : d91285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90087, d91285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90087, d91285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90088 q = 0) : d91286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90088, d91286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90088, d91286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90160 q = 0) : d91346 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90160, d91346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5385 q selected
    | true =>
      simp only [d90160, d91346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5395 q selected
  have h7 (q : Pattern) (selected : d90178 q = 0) : d91364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90178, d91364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5396 q selected
    | true =>
      simp only [d90178, d91364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5397 q selected
  have h8 (q : Pattern) (selected : d90179 q = 0) : d91365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90179, d91365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90179, d91365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90180 q = 0) : d91366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90180, d91366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90180, d91366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d90181 q = 0) : d91367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90181, d91367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90181, d91367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90185 q = 0) : d91371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90185, d91371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90185, d91371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5398 q selected
  have h12 (q : Pattern) (selected : d90187 q = 0) : d91373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90187, d91373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90187, d91373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5399 q selected
  have h13 (q : Pattern) (selected : d90188 q = 0) : d91374 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90188, d91374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90188, d91374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90189 q = 0) : d91375 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90189, d91375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d90189, d91375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d90190 q = 0) : d91376 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90190, d91376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d90190, d91376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d90191 q = 0) : d91377 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90191, d91377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90191, d91377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d90221 q = 0) : d91407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90221, d91407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90221, d91407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5405 q selected
  have h18 (q : Pattern) (selected : d90232 q = 0) : d91414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90232, d91414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90232, d91414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5407 q selected
  have h19 (q : Pattern) (selected : d90233 q = 0) : d91415 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90233, d91415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d90233, d91415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d90234 q = 0) : d91416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90234, d91416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d90234, d91416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d90235 q = 0) : d91417 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90235, d91417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d90235, d91417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d90236 q = 0) : d91418 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90236, d91418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d90236, d91418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d90237 q = 0) : d91419 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d90237, d91419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d90237, d91419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5409 (p : Pattern) (selected : d90243 p = 0) : d91425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90238 q = 0) : d91420 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d90238, d91420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90238, d91420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5408 q selected
  have h2 (q : Pattern) (selected : d90239 q = 0) : d91421 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d90239, d91421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90239, d91421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90240 q = 0) : d91422 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d90240, d91422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90240, d91422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90241 q = 0) : d91423 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d90241, d91423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90241, d91423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90242 q = 0) : d91424 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d90242, d91424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90242, d91424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90243 q = 0) : d91425 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d90243, d91425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90243, d91425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5410 (p : Pattern) (selected : d90249 p = 0) : d91431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90246 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90247 q = 0) : d91429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90248 q = 0) : d91430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90248, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90248, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90249 q = 0) : d91431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90249, d91431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90249, d91431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5411 (p : Pattern) (selected : d90253 p = 0) : d91435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90250 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90251 q = 0) : d91433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90252 q = 0) : d91434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90252, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90252, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90253 q = 0) : d91435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90253, d91435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90253, d91435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5412 (p : Pattern) (selected : d90259 p = 0) : d91441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90254 q = 0) : d91436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90254, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5410 q selected
    | true =>
      simp only [d90254, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5411 q selected
  have h2 (q : Pattern) (selected : d90255 q = 0) : d91437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90255, d91437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90255, d91437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90256 q = 0) : d91438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90256, d91438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90256, d91438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90257 q = 0) : d91439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90257, d91439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90257, d91439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90258 q = 0) : d91440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90258, d91440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90258, d91440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90259 q = 0) : d91441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90259, d91441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90259, d91441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5413 (p : Pattern) (selected : d90262 p = 0) : d91444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90246 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90247 q = 0) : d91429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90248 q = 0) : d91430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90248, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90248, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90262 q = 0) : d91444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90262, d91444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90262, d91444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5414 (p : Pattern) (selected : d90263 p = 0) : d91445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90250 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90251 q = 0) : d91433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90252 q = 0) : d91434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90252, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90252, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90263 q = 0) : d91445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90263, d91445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90263, d91445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5415 (p : Pattern) (selected : d90269 p = 0) : d91451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90254 q = 0) : d91436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90254, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5410 q selected
    | true =>
      simp only [d90254, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5411 q selected
  have h2 (q : Pattern) (selected : d90255 q = 0) : d91437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90255, d91437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90255, d91437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90256 q = 0) : d91438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90256, d91438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90256, d91438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90257 q = 0) : d91439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90257, d91439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90257, d91439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90258 q = 0) : d91440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90258, d91440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90258, d91440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90264 q = 0) : d91446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90264, d91446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5413 q selected
    | true =>
      simp only [d90264, d91446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5414 q selected
  have h7 (q : Pattern) (selected : d90265 q = 0) : d91447 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90265, d91447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90265, d91447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90266 q = 0) : d91448 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90266, d91448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90266, d91448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90267 q = 0) : d91449 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90267, d91449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90267, d91449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90268 q = 0) : d91450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90268, d91450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90268, d91450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90269 q = 0) : d91451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90269, d91451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90269, d91451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5416 (p : Pattern) (selected : d90274 p = 0) : d91456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90246 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90247 q = 0) : d91429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90273 q = 0) : d91455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90273, d91455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90273, d91455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90274 q = 0) : d91456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90274, d91456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90274, d91456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5417 (p : Pattern) (selected : d90276 p = 0) : d91458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90250 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90251 q = 0) : d91433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90275 q = 0) : d91457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90275, d91457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90275, d91457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90276 q = 0) : d91458 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90276, d91458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90276, d91458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5418 (p : Pattern) (selected : d90283 p = 0) : d91465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90246 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90281 q = 0) : d91463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90281, d91463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90281, d91463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90282 q = 0) : d91464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90282, d91464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90282, d91464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90283 q = 0) : d91465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90283, d91465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90283, d91465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5419 (p : Pattern) (selected : d90286 p = 0) : d91468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90250 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90284 q = 0) : d91466 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90284, d91466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90284, d91466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90285 q = 0) : d91467 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90285, d91467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90285, d91467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90286 q = 0) : d91468 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90286, d91468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90286, d91468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5420 (p : Pattern) (selected : d90293 p = 0) : d91475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1222 q = 0) : d52803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro409 q selected
    | true =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6957 q = 0) : d81745 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4260 q selected
    | true =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90290 q = 0) : d91472 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90290, d91472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90290, d91472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90291 q = 0) : d91473 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90291, d91473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90291, d91473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90292 q = 0) : d91474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90292, d91474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90292, d91474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90293 q = 0) : d91475 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90293, d91475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90293, d91475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5421 (p : Pattern) (selected : d90297 p = 0) : d91479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5030 q = 0) : d69120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2801 q selected
    | true =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90294 q = 0) : d91476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90294, d91476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90294, d91476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90295 q = 0) : d91477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90295, d91477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90295, d91477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90296 q = 0) : d91478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90296, d91478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90296, d91478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90297 q = 0) : d91479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90297, d91479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90297, d91479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5422 (p : Pattern) (selected : d90302 p = 0) : d91431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1304 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1304, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro422 q selected
    | true =>
      simp only [d1304, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90299 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90299, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90299, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90300 q = 0) : d91429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90300, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90300, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90301 q = 0) : d91430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90301, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90301, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90302 q = 0) : d91431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90302, d91431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90302, d91431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5423 (p : Pattern) (selected : d90306 p = 0) : d91435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90303 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90303, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90303, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90304 q = 0) : d91433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90304, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90304, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90305 q = 0) : d91434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90305, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90305, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90306 q = 0) : d91435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90306, d91435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90306, d91435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5424 (p : Pattern) (selected : d90312 p = 0) : d91485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90309 q = 0) : d91482 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90309, d91482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90309, d91482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90310 q = 0) : d91483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90310, d91483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90310, d91483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90311 q = 0) : d91484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90311, d91484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90311, d91484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90312 q = 0) : d91485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90312, d91485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90312, d91485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5425 (p : Pattern) (selected : d90318 p = 0) : d91491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90277 q = 0) : d91459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90277, d91459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5416 q selected
    | true =>
      simp only [d90277, d91459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5417 q selected
  have h2 (q : Pattern) (selected : d90278 q = 0) : d91460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90278, d91460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90278, d91460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90279 q = 0) : d91461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90279, d91461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90279, d91461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90280 q = 0) : d91462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90280, d91462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90280, d91462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90287 q = 0) : d91469 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90287, d91469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5418 q selected
    | true =>
      simp only [d90287, d91469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5419 q selected
  have h6 (q : Pattern) (selected : d90288 q = 0) : d91470 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90288, d91470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90288, d91470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90289 q = 0) : d91471 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90289, d91471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90289, d91471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d90298 q = 0) : d91480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90298, d91480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5420 q selected
    | true =>
      simp only [d90298, d91480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5421 q selected
  have h9 (q : Pattern) (selected : d90307 q = 0) : d91436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90307, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5422 q selected
    | true =>
      simp only [d90307, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5423 q selected
  have h10 (q : Pattern) (selected : d90308 q = 0) : d91481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90308, d91481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90308, d91481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90313 q = 0) : d91486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90313, d91486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5424 q selected
    | true =>
      simp only [d90313, d91486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d90314 q = 0) : d91487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90314, d91487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90314, d91487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d90315 q = 0) : d91488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90315, d91488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90315, d91488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90316 q = 0) : d91489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90316, d91489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90316, d91489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d90317 q = 0) : d91490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90317, d91490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90317, d91490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d90318 q = 0) : d91491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90318, d91491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90318, d91491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5426 (p : Pattern) (selected : d90319 p = 0) : d91492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90246 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90247 q = 0) : d91429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90247, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90273 q = 0) : d91455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90273, d91455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90273, d91455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90319 q = 0) : d91492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90319, d91492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90319, d91492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5427 (p : Pattern) (selected : d90320 p = 0) : d91493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90250 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90251 q = 0) : d91433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90251, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90275 q = 0) : d91457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90275, d91457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90275, d91457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90320 q = 0) : d91493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90320, d91493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90320, d91493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5428 (p : Pattern) (selected : d90325 p = 0) : d91498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90246 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90246, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90281 q = 0) : d91463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90281, d91463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90281, d91463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90282 q = 0) : d91464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90282, d91464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90282, d91464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90325 q = 0) : d91498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90325, d91498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90325, d91498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5429 (p : Pattern) (selected : d90326 p = 0) : d91499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90250 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90250, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90284 q = 0) : d91466 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90284, d91466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90284, d91466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90285 q = 0) : d91467 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90285, d91467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90285, d91467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90326 q = 0) : d91499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90326, d91499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90326, d91499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5430 (p : Pattern) (selected : d90330 p = 0) : d91503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1222 q = 0) : d52803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro409 q selected
    | true =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6957 q = 0) : d81745 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4260 q selected
    | true =>
      simp only [d6957, d81745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90290 q = 0) : d91472 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90290, d91472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90290, d91472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90291 q = 0) : d91473 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90291, d91473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90291, d91473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90292 q = 0) : d91474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90292, d91474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90292, d91474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90330 q = 0) : d91503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90330, d91503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90330, d91503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5431 (p : Pattern) (selected : d90331 p = 0) : d91504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5030 q = 0) : d69120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2801 q selected
    | true =>
      simp only [d5030, d69120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90294 q = 0) : d91476 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90294, d91476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90294, d91476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90295 q = 0) : d91477 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90295, d91477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90295, d91477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90296 q = 0) : d91478 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90296, d91478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90296, d91478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90331 q = 0) : d91504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90331, d91504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90331, d91504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5432 (p : Pattern) (selected : d90333 p = 0) : d91444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1304 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1304, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro422 q selected
    | true =>
      simp only [d1304, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90299 q = 0) : d91428 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90299, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90299, d91428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90300 q = 0) : d91429 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90300, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90300, d91429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90301 q = 0) : d91430 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90301, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90301, d91430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90333 q = 0) : d91444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90333, d91444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90333, d91444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5433 (p : Pattern) (selected : d90334 p = 0) : d91445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90303 q = 0) : d91432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90303, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90303, d91432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90304 q = 0) : d91433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90304, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90304, d91433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90305 q = 0) : d91434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90305, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90305, d91434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90334 q = 0) : d91445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90334, d91445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90334, d91445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5434 (p : Pattern) (selected : d90337 p = 0) : d91507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90309 q = 0) : d91482 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90309, d91482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90309, d91482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90310 q = 0) : d91483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90310, d91483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90310, d91483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90311 q = 0) : d91484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90311, d91484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90311, d91484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90337 q = 0) : d91507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90337, d91507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90337, d91507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5435 (p : Pattern) (selected : d90343 p = 0) : d91513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90277 q = 0) : d91459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90277, d91459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5416 q selected
    | true =>
      simp only [d90277, d91459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5417 q selected
  have h2 (q : Pattern) (selected : d90278 q = 0) : d91460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90278, d91460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90278, d91460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90279 q = 0) : d91461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90279, d91461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90279, d91461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90280 q = 0) : d91462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90280, d91462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90280, d91462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90287 q = 0) : d91469 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90287, d91469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5418 q selected
    | true =>
      simp only [d90287, d91469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5419 q selected
  have h6 (q : Pattern) (selected : d90288 q = 0) : d91470 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90288, d91470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90288, d91470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90289 q = 0) : d91471 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90289, d91471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90289, d91471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d90298 q = 0) : d91480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90298, d91480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5420 q selected
    | true =>
      simp only [d90298, d91480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5421 q selected
  have h9 (q : Pattern) (selected : d90307 q = 0) : d91436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90307, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5422 q selected
    | true =>
      simp only [d90307, d91436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5423 q selected
  have h10 (q : Pattern) (selected : d90308 q = 0) : d91481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90308, d91481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90308, d91481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90313 q = 0) : d91486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90313, d91486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5424 q selected
    | true =>
      simp only [d90313, d91486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d90314 q = 0) : d91487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90314, d91487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90314, d91487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d90315 q = 0) : d91488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90315, d91488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90315, d91488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90316 q = 0) : d91489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90316, d91489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90316, d91489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d90317 q = 0) : d91490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90317, d91490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90317, d91490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d90321 q = 0) : d91494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90321, d91494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5426 q selected
    | true =>
      simp only [d90321, d91494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5427 q selected
  have h17 (q : Pattern) (selected : d90322 q = 0) : d91495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90322, d91495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90322, d91495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d90323 q = 0) : d91496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90323, d91496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d90323, d91496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d90324 q = 0) : d91497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90324, d91497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90324, d91497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d90327 q = 0) : d91500 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90327, d91500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5428 q selected
    | true =>
      simp only [d90327, d91500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5429 q selected
  have h21 (q : Pattern) (selected : d90328 q = 0) : d91501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90328, d91501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90328, d91501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d90329 q = 0) : d91502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90329, d91502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d90329, d91502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d90332 q = 0) : d91505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90332, d91505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5430 q selected
    | true =>
      simp only [d90332, d91505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5431 q selected
  have h24 (q : Pattern) (selected : d90335 q = 0) : d91446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90335, d91446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5432 q selected
    | true =>
      simp only [d90335, d91446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5433 q selected
  have h25 (q : Pattern) (selected : d90336 q = 0) : d91506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90336, d91506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d90336, d91506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d90338 q = 0) : d91508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90338, d91508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5434 q selected
    | true =>
      simp only [d90338, d91508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d90339 q = 0) : d91509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90339, d91509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d90339, d91509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d90340 q = 0) : d91510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90340, d91510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d90340, d91510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d90341 q = 0) : d91511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90341, d91511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d90341, d91511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d90342 q = 0) : d91512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90342, d91512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d90342, d91512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d90343 q = 0) : d91513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90343, d91513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d90343, d91513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5436 (p : Pattern) (selected : d90355 p = 0) : d91525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90345 q = 0) : d91515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90345, d91515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5421 q selected
    | true =>
      simp only [d90345, d91515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5411 q selected
  have h2 (q : Pattern) (selected : d90346 q = 0) : d91516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90346, d91516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90346, d91516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90347 q = 0) : d91517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90347, d91517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90347, d91517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90348 q = 0) : d91518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90348, d91518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90348, d91518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90349 q = 0) : d91519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90349, d91519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90349, d91519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90350 q = 0) : d91520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90350, d91520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5411 q selected
    | true =>
      simp only [d90350, d91520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d90351 q = 0) : d91521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90351, d91521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90351, d91521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90352 q = 0) : d91522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90352, d91522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90352, d91522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90353 q = 0) : d91523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90353, d91523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90353, d91523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90354 q = 0) : d91524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90354, d91524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90354, d91524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90355 q = 0) : d91525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90355, d91525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90355, d91525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5437 (p : Pattern) (selected : d90361 p = 0) : d91531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90350 q = 0) : d91520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90350, d91520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5411 q selected
    | true =>
      simp only [d90350, d91520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90351 q = 0) : d91521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90351, d91521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90351, d91521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90352 q = 0) : d91522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90352, d91522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90352, d91522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90353 q = 0) : d91523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90353, d91523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90353, d91523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90354 q = 0) : d91524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90354, d91524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90354, d91524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90356 q = 0) : d91526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90356, d91526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5414 q selected
    | true =>
      simp only [d90356, d91526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d90357 q = 0) : d91527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90357, d91527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90357, d91527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90358 q = 0) : d91528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90358, d91528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90358, d91528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90359 q = 0) : d91529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90359, d91529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90359, d91529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90360 q = 0) : d91530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90360, d91530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90360, d91530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90361 q = 0) : d91531 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90361, d91531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90361, d91531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5438 (p : Pattern) (selected : d90368 p = 0) : d91538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90332 q = 0) : d91505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90332, d91505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5430 q selected
    | true =>
      simp only [d90332, d91505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5431 q selected
  have h2 (q : Pattern) (selected : d90335 q = 0) : d91446 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90335, d91446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5432 q selected
    | true =>
      simp only [d90335, d91446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5433 q selected
  have h3 (q : Pattern) (selected : d90336 q = 0) : d91506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90336, d91506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90336, d91506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90338 q = 0) : d91508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90338, d91508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5434 q selected
    | true =>
      simp only [d90338, d91508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90339 q = 0) : d91509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90339, d91509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90339, d91509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90340 q = 0) : d91510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90340, d91510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90340, d91510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90366 q = 0) : d91536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90366, d91536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90366, d91536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90367 q = 0) : d91537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90367, d91537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90367, d91537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90368 q = 0) : d91538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90368, d91538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90368, d91538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5439 (p : Pattern) (selected : d90370 p = 0) : d91540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90356 q = 0) : d91526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90356, d91526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5414 q selected
    | true =>
      simp only [d90356, d91526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90357 q = 0) : d91527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90357, d91527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90357, d91527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90358 q = 0) : d91528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90358, d91528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90358, d91528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90359 q = 0) : d91529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90359, d91529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90359, d91529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90360 q = 0) : d91530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90360, d91530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90360, d91530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90370 q = 0) : d91540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90370, d91540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90370, d91540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5440 (p : Pattern) (selected : d90379 p = 0) : d91549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1418 q = 0) : d52906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d52906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro443 q selected
    | true =>
      simp only [d1418, d52906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7003 q = 0) : d81791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d81791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4269 q selected
    | true =>
      simp only [d7003, d81791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90376 q = 0) : d91546 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90376, d91546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90376, d91546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90377 q = 0) : d91547 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90377, d91547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90377, d91547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90378 q = 0) : d91548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90378, d91548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90378, d91548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90379 q = 0) : d91549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90379, d91549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90379, d91549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5441 (p : Pattern) (selected : d90383 p = 0) : d91553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6362 q = 0) : d76102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d76102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3662 q selected
    | true =>
      simp only [d6362, d76102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1431 q = 0) : d52919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro446 q selected
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90380 q = 0) : d91550 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90380, d91550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90380, d91550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90381 q = 0) : d91551 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90381, d91551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90381, d91551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90382 q = 0) : d91552 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90382, d91552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90382, d91552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90383 q = 0) : d91553 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90383, d91553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90383, d91553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5442 (p : Pattern) (selected : d90388 p = 0) : d91558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1471 q = 0) : d52911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1471, d52911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro451 q selected
    | true =>
      simp only [d1471, d52911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1475 q = 0) : d52919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1475, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro452 q selected
    | true =>
      simp only [d1475, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90385 q = 0) : d91555 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90385, d91555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90385, d91555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90386 q = 0) : d91556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90386, d91556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90386, d91556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90387 q = 0) : d91557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90387, d91557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90387, d91557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90388 q = 0) : d91558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90388, d91558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90388, d91558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5443 (p : Pattern) (selected : d90392 p = 0) : d91562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1475 q = 0) : d52919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1475, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro452 q selected
    | true =>
      simp only [d1475, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90389 q = 0) : d91559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90389, d91559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90389, d91559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90390 q = 0) : d91560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90390, d91560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90390, d91560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90391 q = 0) : d91561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90391, d91561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90391, d91561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90392 q = 0) : d91562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90392, d91562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90392, d91562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5444 (p : Pattern) (selected : d90398 p = 0) : d91568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1423 q = 0) : d52911 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d52911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro444 q selected
    | true =>
      simp only [d1423, d52911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90395 q = 0) : d91565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90395, d91565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90395, d91565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90396 q = 0) : d91566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90396, d91566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90396, d91566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90397 q = 0) : d91567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90397, d91567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90397, d91567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90398 q = 0) : d91568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90398, d91568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90398, d91568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5445 (p : Pattern) (selected : d90404 p = 0) : d91574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90384 q = 0) : d91554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90384, d91554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5440 q selected
    | true =>
      simp only [d90384, d91554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5441 q selected
  have h2 (q : Pattern) (selected : d90393 q = 0) : d91563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90393, d91563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5442 q selected
    | true =>
      simp only [d90393, d91563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5443 q selected
  have h3 (q : Pattern) (selected : d90394 q = 0) : d91564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90394, d91564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90394, d91564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90399 q = 0) : d91569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90399, d91569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5444 q selected
    | true =>
      simp only [d90399, d91569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90400 q = 0) : d91570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90400, d91570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90400, d91570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90401 q = 0) : d91571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90401, d91571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90401, d91571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90402 q = 0) : d91572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90402, d91572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90402, d91572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90403 q = 0) : d91573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90403, d91573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90403, d91573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90404 q = 0) : d91574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90404, d91574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90404, d91574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5446 (p : Pattern) (selected : d90409 p = 0) : d91562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1431 q = 0) : d52919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro446 q selected
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90406 q = 0) : d91559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90406, d91559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90406, d91559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90407 q = 0) : d91560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90407, d91560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90407, d91560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90408 q = 0) : d91561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90408, d91561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90408, d91561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90409 q = 0) : d91562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90409, d91562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90409, d91562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5447 (p : Pattern) (selected : d90415 p = 0) : d91581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90410 q = 0) : d91576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90410, d91576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5446 q selected
    | true =>
      simp only [d90410, d91576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90411 q = 0) : d91577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90411, d91577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90411, d91577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90412 q = 0) : d91578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90412, d91578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90412, d91578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90413 q = 0) : d91579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90413, d91579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90413, d91579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90414 q = 0) : d91580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90414, d91580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90414, d91580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90415 q = 0) : d91581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90415, d91581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90415, d91581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5448 (p : Pattern) (selected : d90421 p = 0) : d91587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90260 q = 0) : d91442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90260, d91442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90260, d91442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5412 q selected
  have h2 (q : Pattern) (selected : d90261 q = 0) : d91443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90261, d91443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90261, d91443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90270 q = 0) : d91452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90270, d91452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5412 q selected
    | true =>
      simp only [d90270, d91452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5415 q selected
  have h4 (q : Pattern) (selected : d90271 q = 0) : d91453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90271, d91453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90271, d91453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90272 q = 0) : d91454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90272, d91454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90272, d91454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90344 q = 0) : d91514 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90344, d91514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5425 q selected
    | true =>
      simp only [d90344, d91514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5435 q selected
  have h7 (q : Pattern) (selected : d90362 q = 0) : d91532 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90362, d91532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5436 q selected
    | true =>
      simp only [d90362, d91532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5437 q selected
  have h8 (q : Pattern) (selected : d90363 q = 0) : d91533 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90363, d91533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90363, d91533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90364 q = 0) : d91534 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90364, d91534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90364, d91534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d90365 q = 0) : d91535 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90365, d91535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90365, d91535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90369 q = 0) : d91539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90369, d91539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90369, d91539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5438 q selected
  have h12 (q : Pattern) (selected : d90371 q = 0) : d91541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90371, d91541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90371, d91541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5439 q selected
  have h13 (q : Pattern) (selected : d90372 q = 0) : d91542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90372, d91542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90372, d91542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90373 q = 0) : d91543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90373, d91543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d90373, d91543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d90374 q = 0) : d91544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90374, d91544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d90374, d91544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d90375 q = 0) : d91545 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90375, d91545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90375, d91545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d90405 q = 0) : d91575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90405, d91575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90405, d91575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5445 q selected
  have h18 (q : Pattern) (selected : d90416 q = 0) : d91582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90416, d91582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90416, d91582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5447 q selected
  have h19 (q : Pattern) (selected : d90417 q = 0) : d91583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90417, d91583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d90417, d91583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d90418 q = 0) : d91584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90418, d91584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d90418, d91584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d90419 q = 0) : d91585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90419, d91585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d90419, d91585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d90420 q = 0) : d91586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90420, d91586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d90420, d91586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d90421 q = 0) : d91587 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d90421, d91587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d90421, d91587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5449 (p : Pattern) (selected : d90427 p = 0) : d91593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90422 q = 0) : d91588 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d90422, d91588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90422, d91588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5448 q selected
  have h2 (q : Pattern) (selected : d90423 q = 0) : d91589 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d90423, d91589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90423, d91589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90424 q = 0) : d91590 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d90424, d91590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90424, d91590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90425 q = 0) : d91591 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d90425, d91591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90425, d91591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90426 q = 0) : d91592 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d90426, d91592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90426, d91592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90427 q = 0) : d91593 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d90427, d91593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90427, d91593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5450 (p : Pattern) (selected : d90434 p = 0) : d91600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90431 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90432 q = 0) : d91598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90433 q = 0) : d91599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90433, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90433, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90434 q = 0) : d91600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90434, d91600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90434, d91600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5451 (p : Pattern) (selected : d90438 p = 0) : d91604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90435 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90436 q = 0) : d91602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90437 q = 0) : d91603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90437, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90437, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90438 q = 0) : d91604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90438, d91604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90438, d91604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5452 (p : Pattern) (selected : d90444 p = 0) : d91610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90439 q = 0) : d91605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90439, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5450 q selected
    | true =>
      simp only [d90439, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5451 q selected
  have h2 (q : Pattern) (selected : d90440 q = 0) : d91606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90440, d91606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90440, d91606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90441 q = 0) : d91607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90441, d91607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90441, d91607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90442 q = 0) : d91608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90442, d91608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90442, d91608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90443 q = 0) : d91609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90443, d91609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90443, d91609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90444 q = 0) : d91610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90444, d91610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90444, d91610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5453 (p : Pattern) (selected : d90447 p = 0) : d91613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90431 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90432 q = 0) : d91598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90433 q = 0) : d91599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90433, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90433, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90447 q = 0) : d91613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90447, d91613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90447, d91613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5454 (p : Pattern) (selected : d90448 p = 0) : d91614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90435 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90436 q = 0) : d91602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90437 q = 0) : d91603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90437, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90437, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90448 q = 0) : d91614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90448, d91614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90448, d91614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5455 (p : Pattern) (selected : d90454 p = 0) : d91620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90439 q = 0) : d91605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90439, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5450 q selected
    | true =>
      simp only [d90439, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5451 q selected
  have h2 (q : Pattern) (selected : d90440 q = 0) : d91606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90440, d91606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90440, d91606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90441 q = 0) : d91607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90441, d91607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90441, d91607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90442 q = 0) : d91608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90442, d91608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90442, d91608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90443 q = 0) : d91609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90443, d91609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90443, d91609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90449 q = 0) : d91615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90449, d91615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5453 q selected
    | true =>
      simp only [d90449, d91615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5454 q selected
  have h7 (q : Pattern) (selected : d90450 q = 0) : d91616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90450, d91616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90450, d91616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90451 q = 0) : d91617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90451, d91617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90451, d91617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90452 q = 0) : d91618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90452, d91618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90452, d91618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90453 q = 0) : d91619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90453, d91619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90453, d91619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90454 q = 0) : d91620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90454, d91620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90454, d91620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5456 (p : Pattern) (selected : d90459 p = 0) : d91625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90431 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90432 q = 0) : d91598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90458 q = 0) : d91624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90458, d91624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90458, d91624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90459 q = 0) : d91625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90459, d91625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90459, d91625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5457 (p : Pattern) (selected : d90461 p = 0) : d91627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90435 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90436 q = 0) : d91602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90460 q = 0) : d91626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90460, d91626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90460, d91626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90461 q = 0) : d91627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90461, d91627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90461, d91627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5458 (p : Pattern) (selected : d90468 p = 0) : d91634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90431 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90466 q = 0) : d91632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90466, d91632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90466, d91632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90467 q = 0) : d91633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90467, d91633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90467, d91633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90468 q = 0) : d91634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90468, d91634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90468, d91634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5459 (p : Pattern) (selected : d90471 p = 0) : d91637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90435 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90469 q = 0) : d91635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90469, d91635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90469, d91635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90470 q = 0) : d91636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90470, d91636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90470, d91636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90471 q = 0) : d91637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90471, d91637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90471, d91637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5460 (p : Pattern) (selected : d90478 p = 0) : d91644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1677 q = 0) : d53118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro489 q selected
    | true =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7037 q = 0) : d81825 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4275 q selected
    | true =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90475 q = 0) : d91641 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90475, d91641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90475, d91641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90476 q = 0) : d91642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90476, d91642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90476, d91642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90477 q = 0) : d91643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90477, d91643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90477, d91643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90478 q = 0) : d91644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90478, d91644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90478, d91644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5461 (p : Pattern) (selected : d90482 p = 0) : d91648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5146 q = 0) : d69233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2816 q selected
    | true =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90479 q = 0) : d91645 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90479, d91645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90479, d91645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90480 q = 0) : d91646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90480, d91646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90480, d91646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90481 q = 0) : d91647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90481, d91647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90481, d91647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90482 q = 0) : d91648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90482, d91648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90482, d91648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5462 (p : Pattern) (selected : d90487 p = 0) : d91600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1781 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1781, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro508 q selected
    | true =>
      simp only [d1781, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90484 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90484, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90484, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90485 q = 0) : d91598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90485, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90485, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90486 q = 0) : d91599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90486, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90486, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90487 q = 0) : d91600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90487, d91600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90487, d91600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5463 (p : Pattern) (selected : d90491 p = 0) : d91604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90488 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90488, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90488, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90489 q = 0) : d91602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90489, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90489, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90490 q = 0) : d91603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90490, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90490, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90491 q = 0) : d91604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90491, d91604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90491, d91604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5464 (p : Pattern) (selected : d90497 p = 0) : d91654 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90494 q = 0) : d91651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90494, d91651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90494, d91651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90495 q = 0) : d91652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90495, d91652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90495, d91652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90496 q = 0) : d91653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90496, d91653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90496, d91653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90497 q = 0) : d91654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90497, d91654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90497, d91654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5465 (p : Pattern) (selected : d90503 p = 0) : d91660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90462 q = 0) : d91628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90462, d91628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5456 q selected
    | true =>
      simp only [d90462, d91628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5457 q selected
  have h2 (q : Pattern) (selected : d90463 q = 0) : d91629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90463, d91629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90463, d91629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90464 q = 0) : d91630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90464, d91630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90464, d91630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90465 q = 0) : d91631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90465, d91631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90465, d91631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90472 q = 0) : d91638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90472, d91638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5458 q selected
    | true =>
      simp only [d90472, d91638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5459 q selected
  have h6 (q : Pattern) (selected : d90473 q = 0) : d91639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90473, d91639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90473, d91639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90474 q = 0) : d91640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90474, d91640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90474, d91640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d90483 q = 0) : d91649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90483, d91649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5460 q selected
    | true =>
      simp only [d90483, d91649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5461 q selected
  have h9 (q : Pattern) (selected : d90492 q = 0) : d91605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90492, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5462 q selected
    | true =>
      simp only [d90492, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5463 q selected
  have h10 (q : Pattern) (selected : d90493 q = 0) : d91650 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90493, d91650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90493, d91650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90498 q = 0) : d91655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90498, d91655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5464 q selected
    | true =>
      simp only [d90498, d91655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d90499 q = 0) : d91656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90499, d91656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90499, d91656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d90500 q = 0) : d91657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90500, d91657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90500, d91657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90501 q = 0) : d91658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90501, d91658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90501, d91658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d90502 q = 0) : d91659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90502, d91659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90502, d91659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d90503 q = 0) : d91660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90503, d91660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90503, d91660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro5466 (p : Pattern) (selected : d90504 p = 0) : d91661 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90431 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90432 q = 0) : d91598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90432, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90458 q = 0) : d91624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90458, d91624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90458, d91624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90504 q = 0) : d91661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90504, d91661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90504, d91661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5467 (p : Pattern) (selected : d90505 p = 0) : d91662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90435 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90436 q = 0) : d91602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90436, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90460 q = 0) : d91626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90460, d91626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90460, d91626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90505 q = 0) : d91662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90505, d91662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90505, d91662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5468 (p : Pattern) (selected : d90510 p = 0) : d91667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90431 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90431, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90466 q = 0) : d91632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90466, d91632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90466, d91632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90467 q = 0) : d91633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90467, d91633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90467, d91633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90510 q = 0) : d91667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90510, d91667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90510, d91667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5469 (p : Pattern) (selected : d90511 p = 0) : d91668 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90435 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90435, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90469 q = 0) : d91635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90469, d91635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90469, d91635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90470 q = 0) : d91636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90470, d91636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90470, d91636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90511 q = 0) : d91668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90511, d91668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90511, d91668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5470 (p : Pattern) (selected : d90515 p = 0) : d91672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1677 q = 0) : d53118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro489 q selected
    | true =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7037 q = 0) : d81825 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4275 q selected
    | true =>
      simp only [d7037, d81825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90475 q = 0) : d91641 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90475, d91641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90475, d91641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90476 q = 0) : d91642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90476, d91642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90476, d91642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90477 q = 0) : d91643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90477, d91643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90477, d91643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90515 q = 0) : d91672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90515, d91672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90515, d91672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5471 (p : Pattern) (selected : d90516 p = 0) : d91673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5146 q = 0) : d69233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2816 q selected
    | true =>
      simp only [d5146, d69233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90479 q = 0) : d91645 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90479, d91645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90479, d91645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90480 q = 0) : d91646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90480, d91646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90480, d91646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90481 q = 0) : d91647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90481, d91647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90481, d91647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90516 q = 0) : d91673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90516, d91673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90516, d91673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5472 (p : Pattern) (selected : d90518 p = 0) : d91613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1781 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1781, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro508 q selected
    | true =>
      simp only [d1781, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90484 q = 0) : d91597 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90484, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90484, d91597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90485 q = 0) : d91598 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90485, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90485, d91598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90486 q = 0) : d91599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90486, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90486, d91599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90518 q = 0) : d91613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90518, d91613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90518, d91613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5473 (p : Pattern) (selected : d90519 p = 0) : d91614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90488 q = 0) : d91601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90488, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90488, d91601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90489 q = 0) : d91602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90489, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90489, d91602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90490 q = 0) : d91603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90490, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90490, d91603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90519 q = 0) : d91614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90519, d91614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90519, d91614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5474 (p : Pattern) (selected : d90522 p = 0) : d91676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90494 q = 0) : d91651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90494, d91651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90494, d91651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90495 q = 0) : d91652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90495, d91652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90495, d91652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90496 q = 0) : d91653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90496, d91653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90496, d91653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90522 q = 0) : d91676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90522, d91676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90522, d91676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5475 (p : Pattern) (selected : d90528 p = 0) : d91682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90462 q = 0) : d91628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90462, d91628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5456 q selected
    | true =>
      simp only [d90462, d91628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5457 q selected
  have h2 (q : Pattern) (selected : d90463 q = 0) : d91629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90463, d91629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90463, d91629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90464 q = 0) : d91630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90464, d91630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90464, d91630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90465 q = 0) : d91631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90465, d91631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90465, d91631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90472 q = 0) : d91638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90472, d91638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5458 q selected
    | true =>
      simp only [d90472, d91638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5459 q selected
  have h6 (q : Pattern) (selected : d90473 q = 0) : d91639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90473, d91639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90473, d91639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90474 q = 0) : d91640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90474, d91640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90474, d91640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d90483 q = 0) : d91649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90483, d91649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5460 q selected
    | true =>
      simp only [d90483, d91649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5461 q selected
  have h9 (q : Pattern) (selected : d90492 q = 0) : d91605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90492, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5462 q selected
    | true =>
      simp only [d90492, d91605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5463 q selected
  have h10 (q : Pattern) (selected : d90493 q = 0) : d91650 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90493, d91650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90493, d91650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90498 q = 0) : d91655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90498, d91655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5464 q selected
    | true =>
      simp only [d90498, d91655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d90499 q = 0) : d91656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90499, d91656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90499, d91656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d90500 q = 0) : d91657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90500, d91657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90500, d91657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90501 q = 0) : d91658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90501, d91658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90501, d91658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d90502 q = 0) : d91659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90502, d91659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90502, d91659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d90506 q = 0) : d91663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90506, d91663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5466 q selected
    | true =>
      simp only [d90506, d91663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5467 q selected
  have h17 (q : Pattern) (selected : d90507 q = 0) : d91664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90507, d91664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90507, d91664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d90508 q = 0) : d91665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90508, d91665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d90508, d91665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d90509 q = 0) : d91666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90509, d91666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90509, d91666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d90512 q = 0) : d91669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90512, d91669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5468 q selected
    | true =>
      simp only [d90512, d91669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5469 q selected
  have h21 (q : Pattern) (selected : d90513 q = 0) : d91670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90513, d91670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90513, d91670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d90514 q = 0) : d91671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90514, d91671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d90514, d91671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d90517 q = 0) : d91674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90517, d91674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5470 q selected
    | true =>
      simp only [d90517, d91674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5471 q selected
  have h24 (q : Pattern) (selected : d90520 q = 0) : d91615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90520, d91615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5472 q selected
    | true =>
      simp only [d90520, d91615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5473 q selected
  have h25 (q : Pattern) (selected : d90521 q = 0) : d91675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90521, d91675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d90521, d91675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d90523 q = 0) : d91677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90523, d91677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5474 q selected
    | true =>
      simp only [d90523, d91677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d90524 q = 0) : d91678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90524, d91678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d90524, d91678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d90525 q = 0) : d91679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90525, d91679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d90525, d91679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d90526 q = 0) : d91680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90526, d91680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d90526, d91680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d90527 q = 0) : d91681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90527, d91681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d90527, d91681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d90528 q = 0) : d91682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90528, d91682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d90528, d91682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro5476 (p : Pattern) (selected : d90540 p = 0) : d91694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90530 q = 0) : d91684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90530, d91684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5461 q selected
    | true =>
      simp only [d90530, d91684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5451 q selected
  have h2 (q : Pattern) (selected : d90531 q = 0) : d91685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90531, d91685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90531, d91685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90532 q = 0) : d91686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90532, d91686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90532, d91686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90533 q = 0) : d91687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90533, d91687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90533, d91687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90534 q = 0) : d91688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90534, d91688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90534, d91688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90535 q = 0) : d91689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90535, d91689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5451 q selected
    | true =>
      simp only [d90535, d91689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d90536 q = 0) : d91690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90536, d91690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90536, d91690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90537 q = 0) : d91691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90537, d91691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90537, d91691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90538 q = 0) : d91692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90538, d91692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90538, d91692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90539 q = 0) : d91693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90539, d91693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90539, d91693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90540 q = 0) : d91694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90540, d91694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90540, d91694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5477 (p : Pattern) (selected : d90546 p = 0) : d91700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90535 q = 0) : d91689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90535, d91689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5451 q selected
    | true =>
      simp only [d90535, d91689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90536 q = 0) : d91690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90536, d91690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90536, d91690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90537 q = 0) : d91691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90537, d91691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90537, d91691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90538 q = 0) : d91692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90538, d91692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90538, d91692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90539 q = 0) : d91693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90539, d91693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90539, d91693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90541 q = 0) : d91695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90541, d91695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5454 q selected
    | true =>
      simp only [d90541, d91695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d90542 q = 0) : d91696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90542, d91696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90542, d91696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90543 q = 0) : d91697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90543, d91697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90543, d91697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90544 q = 0) : d91698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90544, d91698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90544, d91698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90545 q = 0) : d91699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90545, d91699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90545, d91699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90546 q = 0) : d91700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90546, d91700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90546, d91700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5478 (p : Pattern) (selected : d90553 p = 0) : d91707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90517 q = 0) : d91674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90517, d91674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5470 q selected
    | true =>
      simp only [d90517, d91674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5471 q selected
  have h2 (q : Pattern) (selected : d90520 q = 0) : d91615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90520, d91615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5472 q selected
    | true =>
      simp only [d90520, d91615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5473 q selected
  have h3 (q : Pattern) (selected : d90521 q = 0) : d91675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90521, d91675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90521, d91675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90523 q = 0) : d91677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90523, d91677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5474 q selected
    | true =>
      simp only [d90523, d91677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90524 q = 0) : d91678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90524, d91678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90524, d91678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90525 q = 0) : d91679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90525, d91679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90525, d91679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90551 q = 0) : d91705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90551, d91705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90551, d91705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90552 q = 0) : d91706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90552, d91706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90552, d91706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90553 q = 0) : d91707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90553, d91707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90553, d91707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5479 (p : Pattern) (selected : d90555 p = 0) : d91709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90541 q = 0) : d91695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90541, d91695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5454 q selected
    | true =>
      simp only [d90541, d91695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90542 q = 0) : d91696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90542, d91696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90542, d91696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90543 q = 0) : d91697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90543, d91697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90543, d91697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90544 q = 0) : d91698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90544, d91698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90544, d91698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90545 q = 0) : d91699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90545, d91699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90545, d91699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90555 q = 0) : d91709 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90555, d91709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90555, d91709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5480 (p : Pattern) (selected : d90564 p = 0) : d91718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1895 q = 0) : d53221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d53221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro529 q selected
    | true =>
      simp only [d1895, d53221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d7083 q = 0) : d81871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d81871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4284 q selected
    | true =>
      simp only [d7083, d81871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90561 q = 0) : d91715 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90561, d91715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90561, d91715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90562 q = 0) : d91716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90562, d91716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90562, d91716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90563 q = 0) : d91717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90563, d91717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90563, d91717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90564 q = 0) : d91718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90564, d91718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90564, d91718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5481 (p : Pattern) (selected : d90568 p = 0) : d91722 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6508 q = 0) : d76237 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d76237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3689 q selected
    | true =>
      simp only [d6508, d76237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1908 q = 0) : d53234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro532 q selected
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90565 q = 0) : d91719 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90565, d91719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90565, d91719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90566 q = 0) : d91720 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90566, d91720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90566, d91720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90567 q = 0) : d91721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90567, d91721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90567, d91721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90568 q = 0) : d91722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90568, d91722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90568, d91722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5482 (p : Pattern) (selected : d90573 p = 0) : d91727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1948 q = 0) : d53226 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1948, d53226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro537 q selected
    | true =>
      simp only [d1948, d53226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1952 q = 0) : d53234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1952, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro538 q selected
    | true =>
      simp only [d1952, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90570 q = 0) : d91724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90570, d91724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90570, d91724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90571 q = 0) : d91725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90571, d91725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90571, d91725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90572 q = 0) : d91726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90572, d91726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90572, d91726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90573 q = 0) : d91727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90573, d91727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90573, d91727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5483 (p : Pattern) (selected : d90577 p = 0) : d91731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1952 q = 0) : d53234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1952, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro538 q selected
    | true =>
      simp only [d1952, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90574 q = 0) : d91728 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90574, d91728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90574, d91728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90575 q = 0) : d91729 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90575, d91729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90575, d91729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90576 q = 0) : d91730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90576, d91730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90576, d91730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90577 q = 0) : d91731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90577, d91731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90577, d91731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5484 (p : Pattern) (selected : d90583 p = 0) : d91737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1900 q = 0) : d53226 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d53226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro530 q selected
    | true =>
      simp only [d1900, d53226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90580 q = 0) : d91734 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90580, d91734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90580, d91734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90581 q = 0) : d91735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90581, d91735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90581, d91735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90582 q = 0) : d91736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90582, d91736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90582, d91736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90583 q = 0) : d91737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90583, d91737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90583, d91737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5485 (p : Pattern) (selected : d90589 p = 0) : d91743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90569 q = 0) : d91723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90569, d91723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5480 q selected
    | true =>
      simp only [d90569, d91723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5481 q selected
  have h2 (q : Pattern) (selected : d90578 q = 0) : d91732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90578, d91732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5482 q selected
    | true =>
      simp only [d90578, d91732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5483 q selected
  have h3 (q : Pattern) (selected : d90579 q = 0) : d91733 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90579, d91733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90579, d91733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90584 q = 0) : d91738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90584, d91738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5484 q selected
    | true =>
      simp only [d90584, d91738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90585 q = 0) : d91739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90585, d91739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90585, d91739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90586 q = 0) : d91740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90586, d91740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90586, d91740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d90587 q = 0) : d91741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90587, d91741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90587, d91741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90588 q = 0) : d91742 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90588, d91742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90588, d91742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90589 q = 0) : d91743 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90589, d91743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90589, d91743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro5486 (p : Pattern) (selected : d90594 p = 0) : d91731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1908 q = 0) : d53234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro532 q selected
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90591 q = 0) : d91728 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90591, d91728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90591, d91728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90592 q = 0) : d91729 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90592, d91729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90592, d91729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90593 q = 0) : d91730 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90593, d91730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90593, d91730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90594 q = 0) : d91731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90594, d91731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90594, d91731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5487 (p : Pattern) (selected : d90600 p = 0) : d91750 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90595 q = 0) : d91745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90595, d91745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5486 q selected
    | true =>
      simp only [d90595, d91745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90596 q = 0) : d91746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90596, d91746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90596, d91746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90597 q = 0) : d91747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90597, d91747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90597, d91747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90598 q = 0) : d91748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90598, d91748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90598, d91748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90599 q = 0) : d91749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90599, d91749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90599, d91749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90600 q = 0) : d91750 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90600, d91750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90600, d91750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5488 (p : Pattern) (selected : d90606 p = 0) : d91756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90445 q = 0) : d91611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90445, d91611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90445, d91611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5452 q selected
  have h2 (q : Pattern) (selected : d90446 q = 0) : d91612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90446, d91612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90446, d91612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90455 q = 0) : d91621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90455, d91621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5452 q selected
    | true =>
      simp only [d90455, d91621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5455 q selected
  have h4 (q : Pattern) (selected : d90456 q = 0) : d91622 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90456, d91622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90456, d91622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90457 q = 0) : d91623 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90457, d91623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90457, d91623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90529 q = 0) : d91683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90529, d91683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5465 q selected
    | true =>
      simp only [d90529, d91683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5475 q selected
  have h7 (q : Pattern) (selected : d90547 q = 0) : d91701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90547, d91701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5476 q selected
    | true =>
      simp only [d90547, d91701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5477 q selected
  have h8 (q : Pattern) (selected : d90548 q = 0) : d91702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90548, d91702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d90548, d91702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d90549 q = 0) : d91703 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90549, d91703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d90549, d91703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d90550 q = 0) : d91704 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90550, d91704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90550, d91704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90554 q = 0) : d91708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90554, d91708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90554, d91708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5478 q selected
  have h12 (q : Pattern) (selected : d90556 q = 0) : d91710 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90556, d91710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90556, d91710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5479 q selected
  have h13 (q : Pattern) (selected : d90557 q = 0) : d91711 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90557, d91711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d90557, d91711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d90558 q = 0) : d91712 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90558, d91712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d90558, d91712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d90559 q = 0) : d91713 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90559, d91713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d90559, d91713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d90560 q = 0) : d91714 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90560, d91714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d90560, d91714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d90590 q = 0) : d91744 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90590, d91744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90590, d91744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5485 q selected
  have h18 (q : Pattern) (selected : d90601 q = 0) : d91751 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90601, d91751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90601, d91751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5487 q selected
  have h19 (q : Pattern) (selected : d90602 q = 0) : d91752 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d90602, d91752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d90602, d91752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d90603 q = 0) : d91753 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d90603, d91753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d90603, d91753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d90604 q = 0) : d91754 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d90604, d91754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d90604, d91754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d90605 q = 0) : d91755 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d90605, d91755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d90605, d91755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d90606 q = 0) : d91756 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d90606, d91756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d90606, d91756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro5489 (p : Pattern) (selected : d90612 p = 0) : d91762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90607 q = 0) : d91757 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d90607, d91757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90607, d91757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5488 q selected
  have h2 (q : Pattern) (selected : d90608 q = 0) : d91758 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d90608, d91758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90608, d91758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90609 q = 0) : d91759 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d90609, d91759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90609, d91759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90610 q = 0) : d91760 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d90610, d91760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90610, d91760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90611 q = 0) : d91761 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d90611, d91761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90611, d91761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90612 q = 0) : d91762 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d90612, d91762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90612, d91762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5490 (p : Pattern) (selected : d90620 p = 0) : d91770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90617 q = 0) : d91767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90618 q = 0) : d91768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90618, d91768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90618, d91768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90619 q = 0) : d91769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90619, d91769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90619, d91769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90620 q = 0) : d91770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90620, d91770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90620, d91770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5491 (p : Pattern) (selected : d90624 p = 0) : d91774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90621 q = 0) : d91771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90622 q = 0) : d91772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90622, d91772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90622, d91772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90623 q = 0) : d91773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90623, d91773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90623, d91773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90624 q = 0) : d91774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90624, d91774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90624, d91774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5492 (p : Pattern) (selected : d90630 p = 0) : d91780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90625 q = 0) : d91775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90625, d91775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5490 q selected
    | true =>
      simp only [d90625, d91775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5491 q selected
  have h2 (q : Pattern) (selected : d90626 q = 0) : d91776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90626, d91776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90626, d91776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90627 q = 0) : d91777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90627, d91777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90627, d91777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90628 q = 0) : d91778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90628, d91778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90628, d91778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90629 q = 0) : d91779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90629, d91779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90629, d91779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90630 q = 0) : d91780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90630, d91780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90630, d91780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5493 (p : Pattern) (selected : d90633 p = 0) : d91783 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90617 q = 0) : d91767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90618 q = 0) : d91768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90618, d91768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90618, d91768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90619 q = 0) : d91769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90619, d91769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90619, d91769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90633 q = 0) : d91783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90633, d91783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90633, d91783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro5494 (p : Pattern) (selected : d90634 p = 0) : d91784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90621 q = 0) : d91771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90622 q = 0) : d91772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90622, d91772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90622, d91772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90623 q = 0) : d91773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90623, d91773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90623, d91773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90634 q = 0) : d91784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90634, d91784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90634, d91784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro5495 (p : Pattern) (selected : d90640 p = 0) : d91790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d90625 q = 0) : d91775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90625, d91775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5490 q selected
    | true =>
      simp only [d90625, d91775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5491 q selected
  have h2 (q : Pattern) (selected : d90626 q = 0) : d91776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90626, d91776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90626, d91776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d90627 q = 0) : d91777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90627, d91777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90627, d91777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90628 q = 0) : d91778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90628, d91778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90628, d91778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90629 q = 0) : d91779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90629, d91779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90629, d91779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90635 q = 0) : d91785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d90635, d91785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5493 q selected
    | true =>
      simp only [d90635, d91785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5494 q selected
  have h7 (q : Pattern) (selected : d90636 q = 0) : d91786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d90636, d91786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90636, d91786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d90637 q = 0) : d91787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d90637, d91787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d90637, d91787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d90638 q = 0) : d91788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d90638, d91788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90638, d91788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d90639 q = 0) : d91789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d90639, d91789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90639, d91789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d90640 q = 0) : d91790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d90640, d91790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d90640, d91790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro5496 (p : Pattern) (selected : d90645 p = 0) : d91795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90617 q = 0) : d91767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90618 q = 0) : d91768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90618, d91768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90618, d91768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90644 q = 0) : d91794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90644, d91794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90644, d91794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d90645 q = 0) : d91795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90645, d91795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90645, d91795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5497 (p : Pattern) (selected : d90647 p = 0) : d91797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90621 q = 0) : d91771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90622 q = 0) : d91772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90622, d91772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d90622, d91772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d90646 q = 0) : d91796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90646, d91796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90646, d91796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90647 q = 0) : d91797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90647, d91797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90647, d91797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro5498 (p : Pattern) (selected : d90654 p = 0) : d91804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90617 q = 0) : d91767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90617, d91767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90652 q = 0) : d91802 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90652, d91802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90652, d91802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d90653 q = 0) : d91803 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90653, d91803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d90653, d91803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d90654 q = 0) : d91804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90654, d91804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90654, d91804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro5499 (p : Pattern) (selected : d90657 p = 0) : d91807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d90621 q = 0) : d91771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d90621, d91771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d90655 q = 0) : d91805 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d90655, d91805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90655, d91805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d90656 q = 0) : d91806 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d90656, d91806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d90656, d91806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d90657 q = 0) : d91807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d90657, d91807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d90657, d91807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
end NetHack.Soko22Hazard87
