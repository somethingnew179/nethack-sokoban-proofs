import NetHack.Soko22Hazard87.AndIntroBlocks0170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro42750 (p : Pattern) (ha : d187830 p = 1) (hb : d188486 p = 1) : d181760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187825 q = 1) (hb : d188486 q = 1) : d181755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187825, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187825, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42749 q ha hb
  have h2 (q : Pattern) (ha : d187826 q = 1) (hb : d188486 q = 1) : d181756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187826, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187826, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d187827 q = 1) (hb : d188486 q = 1) : d181757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187827, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187827, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d187828 q = 1) (hb : d188486 q = 1) : d181758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187828, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187828, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d187829 q = 1) (hb : d188486 q = 1) : d181759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187829, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187829, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d187830 q = 1) (hb : d188486 q = 1) : d181760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187830, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187830, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42751 (p : Pattern) (ha : d187836 p = 1) (hb : d188486 p = 1) : d181766 p = 1 := by
  have h0 (q : Pattern) (ha : d187725 q = 1) (hb : d188486 q = 1) : d181655 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187725, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42729 q ha hb
    | true =>
      simp only [d187725, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42732 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d187744 q = 1) (hb : d188486 q = 1) : d181674 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187744, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187744, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42735 q ha hb
  have h3 (q : Pattern) (ha : d187745 q = 1) (hb : d188486 q = 1) : d181675 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187745, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d187745, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d187772 q = 1) (hb : d188486 q = 1) : d181702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187772, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187772, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42740 q ha hb
  have h5 (q : Pattern) (ha : d187773 q = 1) (hb : d188486 q = 1) : d181703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187773, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187773, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d187774 q = 1) (hb : d188486 q = 1) : d181704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187774, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187774, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d187801 q = 1) (hb : d188486 q = 1) : d181731 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187801, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187801, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42745 q ha hb
  have h8 (q : Pattern) (ha : d187802 q = 1) (hb : d188486 q = 1) : d181732 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187802, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187802, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d187803 q = 1) (hb : d188486 q = 1) : d181733 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187803, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187803, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d187804 q = 1) (hb : d188486 q = 1) : d181734 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187804, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187804, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d187831 q = 1) (hb : d188486 q = 1) : d181761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d187831, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187831, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42750 q ha hb
  have h12 (q : Pattern) (ha : d187832 q = 1) (hb : d188486 q = 1) : d181762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d187832, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187832, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d187833 q = 1) (hb : d188486 q = 1) : d181763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d187833, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187833, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d187834 q = 1) (hb : d188486 q = 1) : d181764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d187834, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187834, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d187835 q = 1) (hb : d188486 q = 1) : d181765 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d187835, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d187835, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d187836 q = 1) (hb : d188486 q = 1) : d181766 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d187836, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d187836, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro42752 (p : Pattern) (ha : d187842 p = 1) (hb : d188486 p = 1) : d181772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187837 q = 1) (hb : d188486 q = 1) : d181767 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d187837, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42751 q ha hb
    | true =>
      simp only [d187837, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d187838 q = 1) (hb : d188486 q = 1) : d181768 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d187838, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187838, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d187839 q = 1) (hb : d188486 q = 1) : d181769 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d187839, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187839, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d187840 q = 1) (hb : d188486 q = 1) : d181770 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d187840, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187840, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d187841 q = 1) (hb : d188486 q = 1) : d181771 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d187841, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187841, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d187842 q = 1) (hb : d188486 q = 1) : d181772 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d187842, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187842, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42753 (p : Pattern) (ha : d187848 p = 1) (hb : d188486 p = 1) : d181778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187843 q = 1) (hb : d188486 q = 1) : d181773 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d187843, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42752 q ha hb
    | true =>
      simp only [d187843, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d187844 q = 1) (hb : d188486 q = 1) : d181774 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d187844, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187844, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d187845 q = 1) (hb : d188486 q = 1) : d181775 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d187845, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187845, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d187846 q = 1) (hb : d188486 q = 1) : d181776 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d187846, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187846, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d187847 q = 1) (hb : d188486 q = 1) : d181777 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d187847, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187847, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d187848 q = 1) (hb : d188486 q = 1) : d181778 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d187848, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187848, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42754 (p : Pattern) (ha : d187854 p = 1) (hb : d188486 p = 1) : d181784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187849 q = 1) (hb : d188486 q = 1) : d181779 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d187849, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42753 q ha hb
    | true =>
      simp only [d187849, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d187850 q = 1) (hb : d188486 q = 1) : d181780 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d187850, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187850, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d187851 q = 1) (hb : d188486 q = 1) : d181781 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d187851, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187851, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d187852 q = 1) (hb : d188486 q = 1) : d181782 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d187852, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187852, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d187853 q = 1) (hb : d188486 q = 1) : d181783 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d187853, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187853, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d187854 q = 1) (hb : d188486 q = 1) : d181784 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d187854, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187854, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42755 (p : Pattern) (ha : d187860 p = 1) (hb : d188487 p = 1) : d181790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187855 q = 1) (hb : d188486 q = 1) : d181785 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d187855, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42754 q ha hb
    | true =>
      simp only [d187855, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d187856 q = 1) (hb : d188487 q = 1) : d181786 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d187856, d188487, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187856, d188487, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d187857 q = 1) (hb : d188487 q = 1) : d181787 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d187857, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187857, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d187858 q = 1) (hb : d188487 q = 1) : d181788 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d187858, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187858, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d187859 q = 1) (hb : d188487 q = 1) : d181789 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d187859, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187859, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d187860 q = 1) (hb : d188487 q = 1) : d181790 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d187860, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187860, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro42756 (p : Pattern) (ha : d187866 p = 1) (hb : d188487 p = 1) : d181796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187861 q = 1) (hb : d188487 q = 1) : d181791 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d187861, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42755 q ha hb
    | true =>
      simp only [d187861, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d187862 q = 1) (hb : d188487 q = 1) : d181792 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d187862, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187862, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d187863 q = 1) (hb : d188487 q = 1) : d181793 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d187863, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187863, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d187864 q = 1) (hb : d188487 q = 1) : d181794 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d187864, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187864, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d187865 q = 1) (hb : d188487 q = 1) : d181795 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d187865, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187865, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d187866 q = 1) (hb : d188487 q = 1) : d181796 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d187866, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187866, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42757 (p : Pattern) (ha : d187872 p = 1) (hb : d188487 p = 1) : d181802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187867 q = 1) (hb : d188487 q = 1) : d181797 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d187867, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42756 q ha hb
    | true =>
      simp only [d187867, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d187868 q = 1) (hb : d188487 q = 1) : d181798 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d187868, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187868, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d187869 q = 1) (hb : d188487 q = 1) : d181799 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d187869, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187869, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d187870 q = 1) (hb : d188487 q = 1) : d181800 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d187870, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187870, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d187871 q = 1) (hb : d188487 q = 1) : d181801 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d187871, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187871, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d187872 q = 1) (hb : d188487 q = 1) : d181802 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d187872, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187872, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42758 (p : Pattern) (ha : d187878 p = 1) (hb : d188487 p = 1) : d181808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d188487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d187873 q = 1) (hb : d188487 q = 1) : d181803 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d187873, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42757 q ha hb
    | true =>
      simp only [d187873, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d187874 q = 1) (hb : d188487 q = 1) : d181804 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d187874, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187874, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d187875 q = 1) (hb : d188487 q = 1) : d181805 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d187875, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187875, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d187876 q = 1) (hb : d188487 q = 1) : d181806 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d187876, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187876, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d187877 q = 1) (hb : d188487 q = 1) : d181807 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d187877, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187877, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d187878 q = 1) (hb : d188487 q = 1) : d181808 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d187878, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187878, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42759 (p : Pattern) (ha : d1 p = 1) (hb : d181808 p = 1) : d181808 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d181808 q = 1) : d181808 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro42760 (p : Pattern) (ha : d0 p = 1) (hb : d181808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181808 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro42761 (p : Pattern) (ha : d30 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42762 (p : Pattern) (ha : d18538 p = 1) (hb : d180908 p = 1) : d180912 p = 1 := by
  have h0 (q : Pattern) (ha : d18534 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18535 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18536 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18537 q = 1) (hb : d180908 q = 1) : d180911 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18537, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d18538 q = 1) (hb : d180908 q = 1) : d180912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18538, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18538, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42763 (p : Pattern) (ha : d18548 p = 1) (hb : d180908 p = 1) : d180918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18539 q = 1) (hb : d180908 q = 1) : d180913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
    | true =>
      simp only [d18539, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18540 q = 1) (hb : d180908 q = 1) : d180914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18541 q = 1) (hb : d180908 q = 1) : d180915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18542 q = 1) (hb : d180908 q = 1) : d180916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18542, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18543 q = 1) (hb : d180908 q = 1) : d180917 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18543, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18543, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18544 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18545 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18546 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18547 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18548 q = 1) (hb : d180908 q = 1) : d180918 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18548, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18548, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42764 (p : Pattern) (ha : d18554 p = 1) (hb : d180908 p = 1) : d180924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18549 q = 1) (hb : d180908 q = 1) : d180919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42763 q ha hb
    | true =>
      simp only [d18549, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18550 q = 1) (hb : d180908 q = 1) : d180920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18551 q = 1) (hb : d180908 q = 1) : d180921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18551, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18551, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18552 q = 1) (hb : d180908 q = 1) : d180922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18552, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18552, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18553 q = 1) (hb : d180908 q = 1) : d180923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18553, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18553, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18554 q = 1) (hb : d180908 q = 1) : d180924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18554, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18554, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42765 (p : Pattern) (ha : d18560 p = 1) (hb : d180908 p = 1) : d180930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d180908 q = 1) : d180925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42764 q ha hb
    | true =>
      simp only [d18555, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18556 q = 1) (hb : d180908 q = 1) : d180926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18556, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18557 q = 1) (hb : d180908 q = 1) : d180927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18557, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18557, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18558 q = 1) (hb : d180908 q = 1) : d180928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18558, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18558, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18559 q = 1) (hb : d180908 q = 1) : d180929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18559, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18559, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18560 q = 1) (hb : d180908 q = 1) : d180930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18560, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18560, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42766 (p : Pattern) (ha : d18566 p = 1) (hb : d180908 p = 1) : d180936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18561 q = 1) (hb : d180908 q = 1) : d180931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18561, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18561, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42765 q ha hb
  have h2 (q : Pattern) (ha : d18562 q = 1) (hb : d180908 q = 1) : d180932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18562, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18562, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18563 q = 1) (hb : d180908 q = 1) : d180933 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18563, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18563, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18564 q = 1) (hb : d180908 q = 1) : d180934 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18564, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18564, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18565 q = 1) (hb : d180908 q = 1) : d180935 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18565, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18565, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18566 q = 1) (hb : d180908 q = 1) : d180936 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18566, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18566, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42767 (p : Pattern) (ha : d144 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d141 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d27 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d28 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d143 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d29 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d144 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42768 (p : Pattern) (ha : d18575 p = 1) (hb : d180908 p = 1) : d180944 p = 1 := by
  have h0 (q : Pattern) (ha : d18571 q = 1) (hb : d131097 q = 1) : d18571 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18572 q = 1) (hb : d180908 q = 1) : d180941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18572, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18573 q = 1) (hb : d180908 q = 1) : d180942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18573, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18534 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18535 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18536 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18574 q = 1) (hb : d180908 q = 1) : d180943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18574, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18574, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18537 q = 1) (hb : d180908 q = 1) : d180911 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18537, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18575 q = 1) (hb : d180908 q = 1) : d180944 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18575, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18575, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42769 (p : Pattern) (ha : d18585 p = 1) (hb : d180908 p = 1) : d180950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18576 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
    | true =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
  have h2 (q : Pattern) (ha : d18577 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18578 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18539 q = 1) (hb : d180908 q = 1) : d180913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
    | true =>
      simp only [d18539, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18540 q = 1) (hb : d180908 q = 1) : d180914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18541 q = 1) (hb : d180908 q = 1) : d180915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18579 q = 1) (hb : d180908 q = 1) : d180948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18579, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18542 q = 1) (hb : d180908 q = 1) : d180916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18542, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18580 q = 1) (hb : d180908 q = 1) : d180949 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18580, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18580, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
  have h11 (q : Pattern) (ha : d18581 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18582 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d18544 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18545 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18583 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18546 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d18584 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18585 q = 1) (hb : d180908 q = 1) : d180950 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18585, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18585, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42770 (p : Pattern) (ha : d18591 p = 1) (hb : d180908 p = 1) : d180956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d180908 q = 1) : d180951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42769 q ha hb
    | true =>
      simp only [d18586, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d180908 q = 1) : d180952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18549 q = 1) (hb : d180908 q = 1) : d180919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42763 q ha hb
    | true =>
      simp only [d18549, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18550 q = 1) (hb : d180908 q = 1) : d180920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18588 q = 1) (hb : d180908 q = 1) : d180953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18588, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18588, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18589 q = 1) (hb : d180908 q = 1) : d180954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18589, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18589, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18590 q = 1) (hb : d180908 q = 1) : d180955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18590, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18590, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18591 q = 1) (hb : d180908 q = 1) : d180956 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18591, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18591, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42771 (p : Pattern) (ha : d132592 p = 1) (hb : d180908 p = 1) : d180962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d180908 q = 1) : d180957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42770 q ha hb
    | true =>
      simp only [d18592, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42764 q ha hb
  have h2 (q : Pattern) (ha : d132588 q = 1) (hb : d180908 q = 1) : d180958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132588, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132588, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18555 q = 1) (hb : d180908 q = 1) : d180925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42764 q ha hb
    | true =>
      simp only [d18555, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18556 q = 1) (hb : d180908 q = 1) : d180926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18556, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132589 q = 1) (hb : d180908 q = 1) : d180959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132589, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132589, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132590 q = 1) (hb : d180908 q = 1) : d180960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132590, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132590, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132591 q = 1) (hb : d180908 q = 1) : d180961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132591, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132591, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132592 q = 1) (hb : d180908 q = 1) : d180962 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132592, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132592, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42772 (p : Pattern) (ha : d132598 p = 1) (hb : d180908 p = 1) : d180968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132593 q = 1) (hb : d180908 q = 1) : d180963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132593, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132593, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42771 q ha hb
  have h2 (q : Pattern) (ha : d132594 q = 1) (hb : d180908 q = 1) : d180964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132594, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132594, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132595 q = 1) (hb : d180908 q = 1) : d180965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132595, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132595, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132596 q = 1) (hb : d180908 q = 1) : d180966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132596, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132596, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132597 q = 1) (hb : d180908 q = 1) : d180967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132597, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132597, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132598 q = 1) (hb : d180908 q = 1) : d180968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132598, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132598, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42773 (p : Pattern) (ha : d18695 p = 1) (hb : d180908 p = 1) : d181010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d180908 q = 1) : d180925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42764 q ha hb
    | true =>
      simp only [d18555, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18691 q = 1) (hb : d180908 q = 1) : d181006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18691, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18691, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18692 q = 1) (hb : d180908 q = 1) : d181007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18692, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18692, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18693 q = 1) (hb : d180908 q = 1) : d181008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18693, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18693, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18694 q = 1) (hb : d180908 q = 1) : d181009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18694, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18694, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18695 q = 1) (hb : d180908 q = 1) : d181010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18695, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18695, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42774 (p : Pattern) (ha : d15966 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d321 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d140 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d141 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d142 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d323 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9384 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12493 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d12494 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d27 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42775 (p : Pattern) (ha : d18639 p = 1) (hb : d180908 p = 1) : d180980 p = 1 := by
  have h0 (q : Pattern) (ha : d18631 q = 1) (hb : d131097 q = 1) : d18631 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18632 q = 1) (hb : d180908 q = 1) : d180974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18632, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18632, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18633 q = 1) (hb : d180908 q = 1) : d180975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18633, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18633, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18571 q = 1) (hb : d131097 q = 1) : d18571 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d140 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18572 q = 1) (hb : d180908 q = 1) : d180941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18572, d180908, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18573 q = 1) (hb : d180908 q = 1) : d180942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18573, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18634 q = 1) (hb : d180908 q = 1) : d180976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18634, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18634, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18635 q = 1) (hb : d131097 q = 1) : d18635 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9384 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18636 q = 1) (hb : d180908 q = 1) : d180977 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18636, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d18637 q = 1) (hb : d180908 q = 1) : d180978 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18637, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d18534 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18535 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d18536 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18638 q = 1) (hb : d180908 q = 1) : d180979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18638, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18639 q = 1) (hb : d180908 q = 1) : d180980 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18639, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18639, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42776 (p : Pattern) (ha : d18649 p = 1) (hb : d180908 p = 1) : d180986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18640 q = 1) (hb : d180908 q = 1) : d180981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42775 q ha hb
    | true =>
      simp only [d18640, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
  have h2 (q : Pattern) (ha : d18641 q = 1) (hb : d180908 q = 1) : d180982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18642 q = 1) (hb : d180908 q = 1) : d180983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18576 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
    | true =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
  have h5 (q : Pattern) (ha : d18577 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18578 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18643 q = 1) (hb : d180908 q = 1) : d180984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18643, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18539 q = 1) (hb : d180908 q = 1) : d180913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
    | true =>
      simp only [d18539, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18540 q = 1) (hb : d180908 q = 1) : d180914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18541 q = 1) (hb : d180908 q = 1) : d180915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18579 q = 1) (hb : d180908 q = 1) : d180948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18579, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18644 q = 1) (hb : d180908 q = 1) : d180985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18644, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18644, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15967 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42774 q ha hb
    | true =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
  have h14 (q : Pattern) (ha : d18645 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18646 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
  have h17 (q : Pattern) (ha : d18581 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d18582 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18647 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d31 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d18544 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d18545 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d18583 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d18648 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d18649 q = 1) (hb : d180908 q = 1) : d180986 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18649, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18649, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro42777 (p : Pattern) (ha : d18655 p = 1) (hb : d180908 p = 1) : d180992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18650 q = 1) (hb : d180908 q = 1) : d180987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18650, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42776 q ha hb
    | true =>
      simp only [d18650, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18651 q = 1) (hb : d180908 q = 1) : d180988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18651, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18651, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18586 q = 1) (hb : d180908 q = 1) : d180951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42769 q ha hb
    | true =>
      simp only [d18586, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18587 q = 1) (hb : d180908 q = 1) : d180952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18652 q = 1) (hb : d180908 q = 1) : d180989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18652, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18652, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18653 q = 1) (hb : d180908 q = 1) : d180990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18653, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18653, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18654 q = 1) (hb : d180908 q = 1) : d180991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18654, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18654, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18655 q = 1) (hb : d180908 q = 1) : d180992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18655, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18655, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42778 (p : Pattern) (ha : d18683 p = 1) (hb : d180908 p = 1) : d180998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d180908 q = 1) : d180951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42769 q ha hb
    | true =>
      simp only [d18586, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d180908 q = 1) : d180952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18680 q = 1) (hb : d180908 q = 1) : d180995 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18680, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18680, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18681 q = 1) (hb : d180908 q = 1) : d180996 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18681, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18681, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18682 q = 1) (hb : d180908 q = 1) : d180997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18682, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18682, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18683 q = 1) (hb : d180908 q = 1) : d180998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18683, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18683, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42779 (p : Pattern) (ha : d132608 p = 1) (hb : d180908 p = 1) : d181004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18656 q = 1) (hb : d180908 q = 1) : d180993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18656, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42777 q ha hb
    | true =>
      simp only [d18656, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42770 q ha hb
  have h2 (q : Pattern) (ha : d132604 q = 1) (hb : d180908 q = 1) : d180994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132604, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132604, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18684 q = 1) (hb : d180908 q = 1) : d180999 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18684, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42778 q ha hb
    | true =>
      simp only [d18684, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18685 q = 1) (hb : d180908 q = 1) : d181000 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18685, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18685, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132605 q = 1) (hb : d180908 q = 1) : d181001 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132605, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132605, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132606 q = 1) (hb : d180908 q = 1) : d181002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132606, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132606, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132607 q = 1) (hb : d180908 q = 1) : d181003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132607, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132607, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132608 q = 1) (hb : d180908 q = 1) : d181004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132608, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132608, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42780 (p : Pattern) (ha : d132614 p = 1) (hb : d180908 p = 1) : d181016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132609 q = 1) (hb : d180908 q = 1) : d181005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132609, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132609, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42779 q ha hb
  have h2 (q : Pattern) (ha : d18696 q = 1) (hb : d180908 q = 1) : d181011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42773 q ha hb
  have h3 (q : Pattern) (ha : d132610 q = 1) (hb : d180908 q = 1) : d181012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132610, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132610, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132611 q = 1) (hb : d180908 q = 1) : d181013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132611, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132611, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132612 q = 1) (hb : d180908 q = 1) : d181014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132612, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132612, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132613 q = 1) (hb : d180908 q = 1) : d181015 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132613, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132613, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132614 q = 1) (hb : d180908 q = 1) : d181016 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132614, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132614, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42781 (p : Pattern) (ha : d132620 p = 1) (hb : d180908 p = 1) : d181022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18567 q = 1) (hb : d180908 q = 1) : d180937 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18567, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18567, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42766 q ha hb
  have h2 (q : Pattern) (ha : d18568 q = 1) (hb : d180908 q = 1) : d180938 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18568, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18568, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18569 q = 1) (hb : d180908 q = 1) : d180939 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18569, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18569, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18570 q = 1) (hb : d180908 q = 1) : d180940 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18570, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18570, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132599 q = 1) (hb : d180908 q = 1) : d180969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132599, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132599, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42772 q ha hb
  have h6 (q : Pattern) (ha : d132600 q = 1) (hb : d180908 q = 1) : d180970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132600, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132600, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132601 q = 1) (hb : d180908 q = 1) : d180971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132601, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132601, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132602 q = 1) (hb : d180908 q = 1) : d180972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132602, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132602, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132603 q = 1) (hb : d180908 q = 1) : d180973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132603, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132603, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132615 q = 1) (hb : d180908 q = 1) : d181017 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132615, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132615, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42780 q ha hb
  have h11 (q : Pattern) (ha : d132616 q = 1) (hb : d180908 q = 1) : d181018 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132616, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132616, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d132617 q = 1) (hb : d180908 q = 1) : d181019 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132617, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132617, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d132618 q = 1) (hb : d180908 q = 1) : d181020 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132618, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132618, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d132619 q = 1) (hb : d180908 q = 1) : d181021 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132619, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132619, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d132620 q = 1) (hb : d180908 q = 1) : d181022 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132620, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d132620, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42782 (p : Pattern) (ha : d18751 p = 1) (hb : d180908 p = 1) : d181054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18576 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
    | true =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
  have h2 (q : Pattern) (ha : d18577 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18578 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18738 q = 1) (hb : d180908 q = 1) : d181044 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18738, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18749 q = 1) (hb : d180908 q = 1) : d181053 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18749, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18749, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
  have h7 (q : Pattern) (ha : d18581 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18582 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18740 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18750 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18751 q = 1) (hb : d180908 q = 1) : d181054 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18751, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18751, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42783 (p : Pattern) (ha : d18811 p = 1) (hb : d180908 p = 1) : d181077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18752 q = 1) (hb : d180908 q = 1) : d181055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42782 q ha hb
    | true =>
      simp only [d18752, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18753 q = 1) (hb : d180908 q = 1) : d181056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18808 q = 1) (hb : d180908 q = 1) : d181074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18808, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18808, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18809 q = 1) (hb : d180908 q = 1) : d181075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18809, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18809, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18810 q = 1) (hb : d180908 q = 1) : d181076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18810, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18810, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18811 q = 1) (hb : d180908 q = 1) : d181077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18811, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18811, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42784 (p : Pattern) (ha : d18817 p = 1) (hb : d180908 p = 1) : d181083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18812 q = 1) (hb : d180908 q = 1) : d181078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18812, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42783 q ha hb
    | true =>
      simp only [d18812, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18813 q = 1) (hb : d180908 q = 1) : d181079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18813, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18813, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18814 q = 1) (hb : d180908 q = 1) : d181080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18814, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18814, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18815 q = 1) (hb : d180908 q = 1) : d181081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18815, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18815, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18816 q = 1) (hb : d180908 q = 1) : d181082 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18816, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18816, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18817 q = 1) (hb : d180908 q = 1) : d181083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18817, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18817, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42785 (p : Pattern) (ha : d16077 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d545 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9460 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16073 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16074 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16075 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12748 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d12749 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9384 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12493 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d12494 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d16076 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16077 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42786 (p : Pattern) (ha : d16081 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12493 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d27 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d28 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d12495 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d29 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d16081 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42787 (p : Pattern) (ha : d18719 p = 1) (hb : d180908 p = 1) : d181031 p = 1 := by
  have h0 (q : Pattern) (ha : d18708 q = 1) (hb : d131097 q = 1) : d18708 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18709 q = 1) (hb : d180908 q = 1) : d181023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18710 q = 1) (hb : d180908 q = 1) : d181024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18711 q = 1) (hb : d131097 q = 1) : d18711 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9460 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18712 q = 1) (hb : d180908 q = 1) : d181025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18712, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18712, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18713 q = 1) (hb : d180908 q = 1) : d181026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18713, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18713, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18714 q = 1) (hb : d180908 q = 1) : d181027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18714, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18714, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18715 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18716 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d18717 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d18635 q = 1) (hb : d131097 q = 1) : d18635 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d9384 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18636 q = 1) (hb : d180908 q = 1) : d180977 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18636, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d18637 q = 1) (hb : d180908 q = 1) : d180978 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18637, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18718 q = 1) (hb : d180908 q = 1) : d181030 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18718, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18718, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18719 q = 1) (hb : d180908 q = 1) : d181031 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18719, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18719, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42788 (p : Pattern) (ha : d18723 p = 1) (hb : d180908 p = 1) : d181035 p = 1 := by
  have h0 (q : Pattern) (ha : d18635 q = 1) (hb : d131097 q = 1) : d18635 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9384 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18636 q = 1) (hb : d180908 q = 1) : d180977 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18636, d180908, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18637 q = 1) (hb : d180908 q = 1) : d180978 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18637, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18534 q = 1) (hb : d131097 q = 1) : d18534 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18535 q = 1) (hb : d180908 q = 1) : d180909 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18535, d180908, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18536 q = 1) (hb : d180908 q = 1) : d180910 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18536, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18638 q = 1) (hb : d180908 q = 1) : d180979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18638, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18537 q = 1) (hb : d180908 q = 1) : d180911 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18537, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18723 q = 1) (hb : d180908 q = 1) : d181035 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18723, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18723, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42789 (p : Pattern) (ha : d18735 p = 1) (hb : d180908 p = 1) : d181041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18720 q = 1) (hb : d180908 q = 1) : d181032 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18720, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42787 q ha hb
    | true =>
      simp only [d18720, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42775 q ha hb
  have h2 (q : Pattern) (ha : d18721 q = 1) (hb : d180908 q = 1) : d181033 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18721, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18721, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18722 q = 1) (hb : d180908 q = 1) : d181034 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18722, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18722, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18724 q = 1) (hb : d180908 q = 1) : d181036 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18724, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42775 q ha hb
    | true =>
      simp only [d18724, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42788 q ha hb
  have h5 (q : Pattern) (ha : d18725 q = 1) (hb : d180908 q = 1) : d181037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18725, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18725, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18726 q = 1) (hb : d180908 q = 1) : d181038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18726, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18726, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18727 q = 1) (hb : d180908 q = 1) : d181039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18727, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18727, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18640 q = 1) (hb : d180908 q = 1) : d180981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42775 q ha hb
    | true =>
      simp only [d18640, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
  have h9 (q : Pattern) (ha : d18641 q = 1) (hb : d180908 q = 1) : d180982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18642 q = 1) (hb : d180908 q = 1) : d180983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18576 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
    | true =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
  have h12 (q : Pattern) (ha : d18577 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18578 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18643 q = 1) (hb : d180908 q = 1) : d180984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18643, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18728 q = 1) (hb : d180908 q = 1) : d181040 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18728, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18728, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16078 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42785 q ha hb
    | true =>
      simp only [d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42774 q ha hb
  have h17 (q : Pattern) (ha : d18729 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d18730 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16082 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42774 q ha hb
    | true =>
      simp only [d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42786 q ha hb
  have h20 (q : Pattern) (ha : d18731 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d18732 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d18733 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d15967 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42774 q ha hb
    | true =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
  have h24 (q : Pattern) (ha : d18645 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d18646 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
  have h27 (q : Pattern) (ha : d18581 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d18582 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d18647 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d18734 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d18734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d18735 q = 1) (hb : d180908 q = 1) : d181041 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18735, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18735, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro42790 (p : Pattern) (ha : d18742 p = 1) (hb : d180908 p = 1) : d181046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18640 q = 1) (hb : d180908 q = 1) : d180981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42775 q ha hb
    | true =>
      simp only [d18640, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
  have h2 (q : Pattern) (ha : d18641 q = 1) (hb : d180908 q = 1) : d180982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18642 q = 1) (hb : d180908 q = 1) : d180983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18576 q = 1) (hb : d180908 q = 1) : d180945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42768 q ha hb
    | true =>
      simp only [d18576, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42762 q ha hb
  have h5 (q : Pattern) (ha : d18577 q = 1) (hb : d180908 q = 1) : d180946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18578 q = 1) (hb : d180908 q = 1) : d180947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18643 q = 1) (hb : d180908 q = 1) : d180984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18643, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18738 q = 1) (hb : d180908 q = 1) : d181044 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18738, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18739 q = 1) (hb : d180908 q = 1) : d181045 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18739, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18739, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15967 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42774 q ha hb
    | true =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
  have h11 (q : Pattern) (ha : d18645 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18646 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d145 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42767 q ha hb
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42761 q ha hb
  have h14 (q : Pattern) (ha : d18581 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18582 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18647 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18740 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d18741 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18742 q = 1) (hb : d180908 q = 1) : d181046 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18742, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18742, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42791 (p : Pattern) (ha : d18748 p = 1) (hb : d180908 p = 1) : d181052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18736 q = 1) (hb : d180908 q = 1) : d181042 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18736, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42789 q ha hb
    | true =>
      simp only [d18736, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18737 q = 1) (hb : d180908 q = 1) : d181043 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18737, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18737, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18743 q = 1) (hb : d180908 q = 1) : d181047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42790 q ha hb
    | true =>
      simp only [d18743, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18744 q = 1) (hb : d180908 q = 1) : d181048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18745 q = 1) (hb : d180908 q = 1) : d181049 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18745, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18745, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18746 q = 1) (hb : d180908 q = 1) : d181050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18746, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18746, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18747 q = 1) (hb : d180908 q = 1) : d181051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18747, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18747, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18748 q = 1) (hb : d180908 q = 1) : d181052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18748, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18748, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42792 (p : Pattern) (ha : d18757 p = 1) (hb : d180908 p = 1) : d181060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d180908 q = 1) : d181047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42790 q ha hb
    | true =>
      simp only [d18743, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d180908 q = 1) : d181048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18752 q = 1) (hb : d180908 q = 1) : d181055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42782 q ha hb
    | true =>
      simp only [d18752, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18753 q = 1) (hb : d180908 q = 1) : d181056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18754 q = 1) (hb : d180908 q = 1) : d181057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18754, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18754, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18755 q = 1) (hb : d180908 q = 1) : d181058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18755, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18755, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18756 q = 1) (hb : d180908 q = 1) : d181059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18756, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18756, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18757 q = 1) (hb : d180908 q = 1) : d181060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18757, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18757, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42793 (p : Pattern) (ha : d18800 p = 1) (hb : d180908 p = 1) : d181066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d180908 q = 1) : d181047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42790 q ha hb
    | true =>
      simp only [d18743, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d180908 q = 1) : d181048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18797 q = 1) (hb : d180908 q = 1) : d181063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18797, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18797, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18798 q = 1) (hb : d180908 q = 1) : d181064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18798, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18798, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18799 q = 1) (hb : d180908 q = 1) : d181065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18799, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18799, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18800 q = 1) (hb : d180908 q = 1) : d181066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18800, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18800, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42794 (p : Pattern) (ha : d132625 p = 1) (hb : d180908 p = 1) : d181072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18758 q = 1) (hb : d180908 q = 1) : d181061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18758, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42791 q ha hb
    | true =>
      simp only [d18758, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42792 q ha hb
  have h2 (q : Pattern) (ha : d132621 q = 1) (hb : d180908 q = 1) : d181062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132621, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132621, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18801 q = 1) (hb : d180908 q = 1) : d181067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18801, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42793 q ha hb
    | true =>
      simp only [d18801, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18802 q = 1) (hb : d180908 q = 1) : d181068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18802, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18802, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132622 q = 1) (hb : d180908 q = 1) : d181069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132622, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132622, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132623 q = 1) (hb : d180908 q = 1) : d181070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132623, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132623, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132624 q = 1) (hb : d180908 q = 1) : d181071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132624, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132624, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132625 q = 1) (hb : d180908 q = 1) : d181072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132625, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132625, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42795 (p : Pattern) (ha : d132631 p = 1) (hb : d180908 p = 1) : d181089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132626 q = 1) (hb : d180908 q = 1) : d181073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132626, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132626, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42794 q ha hb
  have h2 (q : Pattern) (ha : d18818 q = 1) (hb : d180908 q = 1) : d181084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18818, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18818, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42784 q ha hb
  have h3 (q : Pattern) (ha : d132627 q = 1) (hb : d180908 q = 1) : d181085 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132627, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132627, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132628 q = 1) (hb : d180908 q = 1) : d181086 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132628, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132628, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132629 q = 1) (hb : d180908 q = 1) : d181087 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132629, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132629, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132630 q = 1) (hb : d180908 q = 1) : d181088 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132630, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132630, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132631 q = 1) (hb : d180908 q = 1) : d181089 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132631, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132631, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42796 (p : Pattern) (ha : d132637 p = 1) (hb : d180908 p = 1) : d181095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132632 q = 1) (hb : d180908 q = 1) : d181090 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132632, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132632, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42795 q ha hb
  have h2 (q : Pattern) (ha : d132633 q = 1) (hb : d180908 q = 1) : d181091 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132633, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132633, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132634 q = 1) (hb : d180908 q = 1) : d181092 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132634, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132634, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132635 q = 1) (hb : d180908 q = 1) : d181093 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132635, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132635, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132636 q = 1) (hb : d180908 q = 1) : d181094 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132636, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132636, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132637 q = 1) (hb : d180908 q = 1) : d181095 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132637, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132637, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42797 (p : Pattern) (ha : d758 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d321 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d753 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d754 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d755 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d757 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d758 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42798 (p : Pattern) (ha : d762 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d753 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42799 (p : Pattern) (ha : d18858 p = 1) (hb : d180908 p = 1) : d181120 p = 1 := by
  have h0 (q : Pattern) (ha : d18631 q = 1) (hb : d131097 q = 1) : d18631 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d320 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18632 q = 1) (hb : d180908 q = 1) : d180974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18632, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18632, d180908, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18633 q = 1) (hb : d180908 q = 1) : d180975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18633, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18633, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18843 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18844 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18845 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18857 q = 1) (hb : d180908 q = 1) : d181119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18857, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18857, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18851 q = 1) (hb : d180908 q = 1) : d181113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18851, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18858 q = 1) (hb : d180908 q = 1) : d181120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18858, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18858, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42800 (p : Pattern) (ha : d18862 p = 1) (hb : d180908 p = 1) : d181124 p = 1 := by
  have h0 (q : Pattern) (ha : d18843 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18844 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18845 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18851 q = 1) (hb : d180908 q = 1) : d181113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18851, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d18862 q = 1) (hb : d180908 q = 1) : d181124 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18862, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18862, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42801 (p : Pattern) (ha : d18895 p = 1) (hb : d180908 p = 1) : d181143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18863 q = 1) (hb : d180908 q = 1) : d181125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42799 q ha hb
    | true =>
      simp only [d18863, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42800 q ha hb
  have h2 (q : Pattern) (ha : d18864 q = 1) (hb : d180908 q = 1) : d181126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18865 q = 1) (hb : d180908 q = 1) : d181127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18882 q = 1) (hb : d180908 q = 1) : d181133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18882, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18893 q = 1) (hb : d180908 q = 1) : d181142 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18893, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18893, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d763 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42797 q ha hb
    | true =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42798 q ha hb
  have h7 (q : Pattern) (ha : d18875 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18876 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18884 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d18894 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18895 q = 1) (hb : d180908 q = 1) : d181143 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18895, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18895, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42802 (p : Pattern) (ha : d18970 p = 1) (hb : d180908 p = 1) : d181166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18896 q = 1) (hb : d180908 q = 1) : d181144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42801 q ha hb
    | true =>
      simp only [d18896, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18897 q = 1) (hb : d180908 q = 1) : d181145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18967 q = 1) (hb : d180908 q = 1) : d181163 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18967, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18967, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18968 q = 1) (hb : d180908 q = 1) : d181164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18968, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18968, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18969 q = 1) (hb : d180908 q = 1) : d181165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18969, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18969, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18970 q = 1) (hb : d180908 q = 1) : d181166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18970, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18970, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42803 (p : Pattern) (ha : d18976 p = 1) (hb : d180908 p = 1) : d181172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18971 q = 1) (hb : d180908 q = 1) : d181167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18971, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42802 q ha hb
    | true =>
      simp only [d18971, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18972 q = 1) (hb : d180908 q = 1) : d181168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18972, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18972, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18973 q = 1) (hb : d180908 q = 1) : d181169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18973, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18973, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18974 q = 1) (hb : d180908 q = 1) : d181170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18974, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18974, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18975 q = 1) (hb : d180908 q = 1) : d181171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18975, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18975, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18976 q = 1) (hb : d180908 q = 1) : d181172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18976, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18976, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42804 (p : Pattern) (ha : d16227 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d545 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9460 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16073 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16074 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16075 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12748 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d12749 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d753 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d754 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d12750 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16227 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42805 (p : Pattern) (ha : d16274 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d835 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d836 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9589 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16270 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16270, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16271 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16272 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9599 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14529 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14529, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14530 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12748 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d12749 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d16273 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16274 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42806 (p : Pattern) (ha : d16278 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12748 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d753 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d754 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d12750 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d757 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d16278 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42807 (p : Pattern) (ha : d18842 p = 1) (hb : d180908 p = 1) : d181105 p = 1 := by
  have h0 (q : Pattern) (ha : d18831 q = 1) (hb : d131097 q = 1) : d18831 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d835 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18832 q = 1) (hb : d180908 q = 1) : d181097 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18832, d180908, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18832, d180908, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18833 q = 1) (hb : d180908 q = 1) : d181098 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18833, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18833, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18834 q = 1) (hb : d131097 q = 1) : d18834 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9589 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18835 q = 1) (hb : d180908 q = 1) : d181099 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18835, d180908, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18835, d180908, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18836 q = 1) (hb : d180908 q = 1) : d181100 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18836, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18836, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18837 q = 1) (hb : d180908 q = 1) : d181101 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18837, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18837, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18838 q = 1) (hb : d131097 q = 1) : d18838 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9599 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18839 q = 1) (hb : d180908 q = 1) : d181102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18839, d180908, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18839, d180908, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d18840 q = 1) (hb : d180908 q = 1) : d181103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18840, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18840, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d18715 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18716 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d18717 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18841 q = 1) (hb : d180908 q = 1) : d181104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18841, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18841, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18842 q = 1) (hb : d180908 q = 1) : d181105 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18842, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18842, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42808 (p : Pattern) (ha : d18847 p = 1) (hb : d180908 p = 1) : d181109 p = 1 := by
  have h0 (q : Pattern) (ha : d18708 q = 1) (hb : d131097 q = 1) : d18708 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d544 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18709 q = 1) (hb : d180908 q = 1) : d181023 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18709, d180908, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18710 q = 1) (hb : d180908 q = 1) : d181024 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18710, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18711 q = 1) (hb : d131097 q = 1) : d18711 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9460 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18712 q = 1) (hb : d180908 q = 1) : d181025 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18712, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18712, d180908, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18713 q = 1) (hb : d180908 q = 1) : d181026 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18713, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18713, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18714 q = 1) (hb : d180908 q = 1) : d181027 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18714, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18714, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18715 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18716 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d18717 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d18843 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18844 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d18845 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d18846 q = 1) (hb : d180908 q = 1) : d181108 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18846, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18846, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18847 q = 1) (hb : d180908 q = 1) : d181109 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18847, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18847, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42809 (p : Pattern) (ha : d18852 p = 1) (hb : d180908 p = 1) : d181114 p = 1 := by
  have h0 (q : Pattern) (ha : d18715 q = 1) (hb : d131097 q = 1) : d18715 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9470 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18716 q = 1) (hb : d180908 q = 1) : d181028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18716, d180908, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18717 q = 1) (hb : d180908 q = 1) : d181029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18717, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18843 q = 1) (hb : d131097 q = 1) : d18843 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d752 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18844 q = 1) (hb : d180908 q = 1) : d181106 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18844, d180908, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18845 q = 1) (hb : d180908 q = 1) : d181107 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18845, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18846 q = 1) (hb : d180908 q = 1) : d181108 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18846, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18846, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18851 q = 1) (hb : d180908 q = 1) : d181113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18851, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18852 q = 1) (hb : d180908 q = 1) : d181114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18852, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18852, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42810 (p : Pattern) (ha : d18879 p = 1) (hb : d180908 p = 1) : d181130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18848 q = 1) (hb : d180908 q = 1) : d181110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18848, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42807 q ha hb
    | true =>
      simp only [d18848, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42808 q ha hb
  have h2 (q : Pattern) (ha : d18849 q = 1) (hb : d180908 q = 1) : d181111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18849, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18849, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18850 q = 1) (hb : d180908 q = 1) : d181112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18850, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18850, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18853 q = 1) (hb : d180908 q = 1) : d181115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18853, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42808 q ha hb
    | true =>
      simp only [d18853, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42809 q ha hb
  have h5 (q : Pattern) (ha : d18854 q = 1) (hb : d180908 q = 1) : d181116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18854, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18854, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18855 q = 1) (hb : d180908 q = 1) : d181117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18855, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18855, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18856 q = 1) (hb : d180908 q = 1) : d181118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18856, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18856, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18859 q = 1) (hb : d180908 q = 1) : d181121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18859, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42808 q ha hb
    | true =>
      simp only [d18859, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42799 q ha hb
  have h9 (q : Pattern) (ha : d18860 q = 1) (hb : d180908 q = 1) : d181122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18860, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18861 q = 1) (hb : d180908 q = 1) : d181123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18863 q = 1) (hb : d180908 q = 1) : d181125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42799 q ha hb
    | true =>
      simp only [d18863, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42800 q ha hb
  have h12 (q : Pattern) (ha : d18864 q = 1) (hb : d180908 q = 1) : d181126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18865 q = 1) (hb : d180908 q = 1) : d181127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18866 q = 1) (hb : d180908 q = 1) : d181128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18866, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18867 q = 1) (hb : d180908 q = 1) : d181129 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18867, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18867, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16275 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42805 q ha hb
    | true =>
      simp only [d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42804 q ha hb
  have h17 (q : Pattern) (ha : d18868 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d18869 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16279 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42804 q ha hb
    | true =>
      simp only [d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42806 q ha hb
  have h20 (q : Pattern) (ha : d18870 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d18870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d18871 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d18872 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16228 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42804 q ha hb
    | true =>
      simp only [d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42797 q ha hb
  have h24 (q : Pattern) (ha : d18873 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d18874 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d763 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42797 q ha hb
    | true =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42798 q ha hb
  have h27 (q : Pattern) (ha : d18875 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d18876 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d18877 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d18878 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d18878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d18879 q = 1) (hb : d180908 q = 1) : d181130 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18879, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18879, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro42811 (p : Pattern) (ha : d18886 p = 1) (hb : d180908 p = 1) : d181135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18859 q = 1) (hb : d180908 q = 1) : d181121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18859, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42808 q ha hb
    | true =>
      simp only [d18859, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42799 q ha hb
  have h2 (q : Pattern) (ha : d18860 q = 1) (hb : d180908 q = 1) : d181122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18860, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18861 q = 1) (hb : d180908 q = 1) : d181123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18863 q = 1) (hb : d180908 q = 1) : d181125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42799 q ha hb
    | true =>
      simp only [d18863, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42800 q ha hb
  have h5 (q : Pattern) (ha : d18864 q = 1) (hb : d180908 q = 1) : d181126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18865 q = 1) (hb : d180908 q = 1) : d181127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18866 q = 1) (hb : d180908 q = 1) : d181128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18866, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18882 q = 1) (hb : d180908 q = 1) : d181133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18882, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18883 q = 1) (hb : d180908 q = 1) : d181134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18883, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18883, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16228 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42804 q ha hb
    | true =>
      simp only [d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42797 q ha hb
  have h11 (q : Pattern) (ha : d18873 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18874 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d763 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42797 q ha hb
    | true =>
      simp only [d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42798 q ha hb
  have h14 (q : Pattern) (ha : d18875 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d18876 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18877 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18884 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d18885 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18886 q = 1) (hb : d180908 q = 1) : d181135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18886, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18886, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42812 (p : Pattern) (ha : d18892 p = 1) (hb : d180908 p = 1) : d181141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18880 q = 1) (hb : d180908 q = 1) : d181131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18880, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42810 q ha hb
    | true =>
      simp only [d18880, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18881 q = 1) (hb : d180908 q = 1) : d181132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18881, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18881, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18887 q = 1) (hb : d180908 q = 1) : d181136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42811 q ha hb
    | true =>
      simp only [d18887, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18888 q = 1) (hb : d180908 q = 1) : d181137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18889 q = 1) (hb : d180908 q = 1) : d181138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18889, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18889, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18890 q = 1) (hb : d180908 q = 1) : d181139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18890, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18890, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18891 q = 1) (hb : d180908 q = 1) : d181140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18891, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18891, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18892 q = 1) (hb : d180908 q = 1) : d181141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18892, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18892, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42813 (p : Pattern) (ha : d18901 p = 1) (hb : d180908 p = 1) : d181149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d180908 q = 1) : d181136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42811 q ha hb
    | true =>
      simp only [d18887, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d180908 q = 1) : d181137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18896 q = 1) (hb : d180908 q = 1) : d181144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42801 q ha hb
    | true =>
      simp only [d18896, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18897 q = 1) (hb : d180908 q = 1) : d181145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18898 q = 1) (hb : d180908 q = 1) : d181146 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18898, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18898, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18899 q = 1) (hb : d180908 q = 1) : d181147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18899, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18899, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18900 q = 1) (hb : d180908 q = 1) : d181148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18900, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18900, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18901 q = 1) (hb : d180908 q = 1) : d181149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18901, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18901, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42814 (p : Pattern) (ha : d18959 p = 1) (hb : d180908 p = 1) : d181155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d180908 q = 1) : d181136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42811 q ha hb
    | true =>
      simp only [d18887, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d180908 q = 1) : d181137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18956 q = 1) (hb : d180908 q = 1) : d181152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18956, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18956, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18957 q = 1) (hb : d180908 q = 1) : d181153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18957, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18957, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18958 q = 1) (hb : d180908 q = 1) : d181154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18958, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18958, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18959 q = 1) (hb : d180908 q = 1) : d181155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18959, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18959, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42815 (p : Pattern) (ha : d132643 p = 1) (hb : d180908 p = 1) : d181161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18902 q = 1) (hb : d180908 q = 1) : d181150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18902, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42812 q ha hb
    | true =>
      simp only [d18902, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42813 q ha hb
  have h2 (q : Pattern) (ha : d132639 q = 1) (hb : d180908 q = 1) : d181151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132639, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132639, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18960 q = 1) (hb : d180908 q = 1) : d181156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18960, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42814 q ha hb
    | true =>
      simp only [d18960, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18961 q = 1) (hb : d180908 q = 1) : d181157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18961, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18961, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132640 q = 1) (hb : d180908 q = 1) : d181158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132640, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132640, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132641 q = 1) (hb : d180908 q = 1) : d181159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132641, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132641, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132642 q = 1) (hb : d180908 q = 1) : d181160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132642, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132642, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132643 q = 1) (hb : d180908 q = 1) : d181161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132643, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132643, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42816 (p : Pattern) (ha : d132649 p = 1) (hb : d180908 p = 1) : d181178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132644 q = 1) (hb : d180908 q = 1) : d181162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132644, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132644, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42815 q ha hb
  have h2 (q : Pattern) (ha : d18977 q = 1) (hb : d180908 q = 1) : d181173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18977, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18977, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42803 q ha hb
  have h3 (q : Pattern) (ha : d132645 q = 1) (hb : d180908 q = 1) : d181174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132645, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132645, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132646 q = 1) (hb : d180908 q = 1) : d181175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132646, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132646, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132647 q = 1) (hb : d180908 q = 1) : d181176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132647, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132647, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132648 q = 1) (hb : d180908 q = 1) : d181177 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132648, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132648, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132649 q = 1) (hb : d180908 q = 1) : d181178 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132649, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132649, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42817 (p : Pattern) (ha : d132655 p = 1) (hb : d180908 p = 1) : d181184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132650 q = 1) (hb : d180908 q = 1) : d181179 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132650, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132650, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42816 q ha hb
  have h2 (q : Pattern) (ha : d132651 q = 1) (hb : d180908 q = 1) : d181180 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132651, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132651, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132652 q = 1) (hb : d180908 q = 1) : d181181 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132652, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132652, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132653 q = 1) (hb : d180908 q = 1) : d181182 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132653, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132653, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132654 q = 1) (hb : d180908 q = 1) : d181183 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132654, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132654, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132655 q = 1) (hb : d180908 q = 1) : d181184 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132655, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132655, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42818 (p : Pattern) (ha : d14778 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1123 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9846 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14770 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d14771 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d14772 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d14778 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42819 (p : Pattern) (ha : d16443 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1112 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1123 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1124 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d1125 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9802 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14763 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14764 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d14765 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d16443 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42820 (p : Pattern) (ha : d19038 p = 1) (hb : d180908 p = 1) : d181224 p = 1 := by
  have h0 (q : Pattern) (ha : d19031 q = 1) (hb : d131097 q = 1) : d19031 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19032 q = 1) (hb : d180908 q = 1) : d181219 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19032, d180908, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19032, d180908, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19033 q = 1) (hb : d180908 q = 1) : d181220 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19033, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19033, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19034 q = 1) (hb : d131097 q = 1) : d19034 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19035 q = 1) (hb : d180908 q = 1) : d181221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19035, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19036 q = 1) (hb : d180908 q = 1) : d181222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19036, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19037 q = 1) (hb : d180908 q = 1) : d181223 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19037, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19037, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19013 q = 1) (hb : d131097 q = 1) : d19013 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9802 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19014 q = 1) (hb : d180908 q = 1) : d181203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19014, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19015 q = 1) (hb : d180908 q = 1) : d181204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19015, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19025 q = 1) (hb : d180908 q = 1) : d181213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19025, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19025, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d19038 q = 1) (hb : d180908 q = 1) : d181224 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19038, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19038, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42821 (p : Pattern) (ha : d19082 p = 1) (hb : d180908 p = 1) : d181253 p = 1 := by
  have h0 (q : Pattern) (ha : d19034 q = 1) (hb : d131097 q = 1) : d19034 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19035 q = 1) (hb : d180908 q = 1) : d181221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19035, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19036 q = 1) (hb : d180908 q = 1) : d181222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19036, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19081 q = 1) (hb : d180908 q = 1) : d181252 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19081, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19081, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19046 q = 1) (hb : d131097 q = 1) : d19046 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9846 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19047 q = 1) (hb : d180908 q = 1) : d181231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19047, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19047, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d19048 q = 1) (hb : d180908 q = 1) : d181232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19048, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19048, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d19049 q = 1) (hb : d180908 q = 1) : d181233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19049, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19049, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19082 q = 1) (hb : d180908 q = 1) : d181253 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19082, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19082, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42822 (p : Pattern) (ha : d19092 p = 1) (hb : d180908 p = 1) : d181259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19083 q = 1) (hb : d180908 q = 1) : d181254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19083, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
    | true =>
      simp only [d19083, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42821 q ha hb
  have h2 (q : Pattern) (ha : d19084 q = 1) (hb : d180908 q = 1) : d181255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19084, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19085 q = 1) (hb : d180908 q = 1) : d181256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19086 q = 1) (hb : d180908 q = 1) : d181257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19086, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19087 q = 1) (hb : d180908 q = 1) : d181258 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19087, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19087, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16451 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
    | true =>
      simp only [d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42818 q ha hb
  have h7 (q : Pattern) (ha : d19088 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19089 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19090 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19091 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19092 q = 1) (hb : d180908 q = 1) : d181259 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19092, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19092, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42823 (p : Pattern) (ha : d19201 p = 1) (hb : d180908 p = 1) : d181291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19093 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42822 q ha hb
    | true =>
      simp only [d19093, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19094 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19198 q = 1) (hb : d180908 q = 1) : d181288 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19198, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19198, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19199 q = 1) (hb : d180908 q = 1) : d181289 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19199, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19199, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19200 q = 1) (hb : d180908 q = 1) : d181290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19200, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19200, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19201 q = 1) (hb : d180908 q = 1) : d181291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19201, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19201, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42824 (p : Pattern) (ha : d19207 p = 1) (hb : d180908 p = 1) : d181297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19202 q = 1) (hb : d180908 q = 1) : d181292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19202, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42823 q ha hb
    | true =>
      simp only [d19202, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19203 q = 1) (hb : d180908 q = 1) : d181293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19203, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19203, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19204 q = 1) (hb : d180908 q = 1) : d181294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19204, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19204, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19205 q = 1) (hb : d180908 q = 1) : d181295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19205, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19205, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19206 q = 1) (hb : d180908 q = 1) : d181296 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19206, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19206, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19207 q = 1) (hb : d180908 q = 1) : d181297 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19207, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19207, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42825 (p : Pattern) (ha : d14773 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5020 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9846 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14770 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d14771 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d14772 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d14773 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42826 (p : Pattern) (ha : d16442 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1102 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9791 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16438 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16438, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16439 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16440 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14758 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14759 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9802 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14763 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d14764 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d16441 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16442 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42827 (p : Pattern) (ha : d16511 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1211 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1212 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9755 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16507 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16507, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16507, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16508 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16509 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9765 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14836 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14836, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14836, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14837 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d9780 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14758 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d14759 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d16510 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16511 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42828 (p : Pattern) (ha : d16516 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13022 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13022, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13023 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9802 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14763 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14764 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16515 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14765 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d16516 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42829 (p : Pattern) (ha : d19005 p = 1) (hb : d180908 p = 1) : d181197 p = 1 := by
  have h0 (q : Pattern) (ha : d18991 q = 1) (hb : d131097 q = 1) : d18991 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1211 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18992 q = 1) (hb : d180908 q = 1) : d181187 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18992, d180908, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18992, d180908, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18993 q = 1) (hb : d180908 q = 1) : d181188 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18993, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18993, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18994 q = 1) (hb : d131097 q = 1) : d18994 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9755 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18995 q = 1) (hb : d180908 q = 1) : d181189 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18995, d180908, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18995, d180908, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d18996 q = 1) (hb : d180908 q = 1) : d181190 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18996, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18996, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d18997 q = 1) (hb : d180908 q = 1) : d181191 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18997, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18997, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18998 q = 1) (hb : d131097 q = 1) : d18998 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9765 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d18999 q = 1) (hb : d180908 q = 1) : d181192 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18999, d180908, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18999, d180908, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19000 q = 1) (hb : d180908 q = 1) : d181193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19000, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19000, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19001 q = 1) (hb : d131097 q = 1) : d19001 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d9780 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19002 q = 1) (hb : d180908 q = 1) : d181194 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19002, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19002, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d19003 q = 1) (hb : d180908 q = 1) : d181195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19003, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19003, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19004 q = 1) (hb : d180908 q = 1) : d181196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19004, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19004, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19005 q = 1) (hb : d180908 q = 1) : d181197 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19005, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19005, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42830 (p : Pattern) (ha : d19017 p = 1) (hb : d180908 p = 1) : d181206 p = 1 := by
  have h0 (q : Pattern) (ha : d19006 q = 1) (hb : d131097 q = 1) : d19006 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19007 q = 1) (hb : d180908 q = 1) : d181198 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19007, d180908, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19007, d180908, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19008 q = 1) (hb : d180908 q = 1) : d181199 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19008, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19008, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19009 q = 1) (hb : d131097 q = 1) : d19009 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9791 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19010 q = 1) (hb : d180908 q = 1) : d181200 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19010, d180908, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19010, d180908, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19011 q = 1) (hb : d180908 q = 1) : d181201 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19011, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19011, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19012 q = 1) (hb : d180908 q = 1) : d181202 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19012, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19012, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19001 q = 1) (hb : d131097 q = 1) : d19001 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9780 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19002 q = 1) (hb : d180908 q = 1) : d181194 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19002, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19002, d180908, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19003 q = 1) (hb : d180908 q = 1) : d181195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19003, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19003, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19013 q = 1) (hb : d131097 q = 1) : d19013 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d9802 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19014 q = 1) (hb : d180908 q = 1) : d181203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19014, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d19015 q = 1) (hb : d180908 q = 1) : d181204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19015, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19016 q = 1) (hb : d180908 q = 1) : d181205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19016, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19016, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19017 q = 1) (hb : d180908 q = 1) : d181206 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19017, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19017, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42831 (p : Pattern) (ha : d19026 p = 1) (hb : d180908 p = 1) : d181214 p = 1 := by
  have h0 (q : Pattern) (ha : d19021 q = 1) (hb : d131097 q = 1) : d19021 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19022 q = 1) (hb : d180908 q = 1) : d181210 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19022, d180908, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19022, d180908, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19023 q = 1) (hb : d180908 q = 1) : d181211 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19023, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19023, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19013 q = 1) (hb : d131097 q = 1) : d19013 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9802 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19014 q = 1) (hb : d180908 q = 1) : d181203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19014, d180908, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19015 q = 1) (hb : d180908 q = 1) : d181204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19015, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19024 q = 1) (hb : d180908 q = 1) : d181212 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19024, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19024, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19025 q = 1) (hb : d180908 q = 1) : d181213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19025, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19025, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19026 q = 1) (hb : d180908 q = 1) : d181214 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19026, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19026, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42832 (p : Pattern) (ha : d19050 p = 1) (hb : d180908 p = 1) : d181234 p = 1 := by
  have h0 (q : Pattern) (ha : d19042 q = 1) (hb : d131097 q = 1) : d19042 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19043 q = 1) (hb : d180908 q = 1) : d181228 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19043, d180908, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19043, d180908, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19044 q = 1) (hb : d180908 q = 1) : d181229 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19044, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19044, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19045 q = 1) (hb : d180908 q = 1) : d181230 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19045, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19045, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19046 q = 1) (hb : d131097 q = 1) : d19046 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9846 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19047 q = 1) (hb : d180908 q = 1) : d181231 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19047, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19047, d180908, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d19048 q = 1) (hb : d180908 q = 1) : d181232 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19048, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19048, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d19049 q = 1) (hb : d180908 q = 1) : d181233 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19049, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19049, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19050 q = 1) (hb : d180908 q = 1) : d181234 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19050, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19050, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42833 (p : Pattern) (ha : d19067 p = 1) (hb : d180908 p = 1) : d181240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19018 q = 1) (hb : d180908 q = 1) : d181207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19018, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42829 q ha hb
    | true =>
      simp only [d19018, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42830 q ha hb
  have h2 (q : Pattern) (ha : d19019 q = 1) (hb : d180908 q = 1) : d181208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19019, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19019, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19020 q = 1) (hb : d180908 q = 1) : d181209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19020, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19020, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19027 q = 1) (hb : d180908 q = 1) : d181215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19027, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42830 q ha hb
    | true =>
      simp only [d19027, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42831 q ha hb
  have h5 (q : Pattern) (ha : d19028 q = 1) (hb : d180908 q = 1) : d181216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19028, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19028, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19029 q = 1) (hb : d180908 q = 1) : d181217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19029, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19029, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19030 q = 1) (hb : d180908 q = 1) : d181218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19030, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19030, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19039 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42830 q ha hb
    | true =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
  have h9 (q : Pattern) (ha : d19040 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19041 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19051 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
    | true =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42832 q ha hb
  have h12 (q : Pattern) (ha : d19052 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19053 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19054 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19055 q = 1) (hb : d180908 q = 1) : d181239 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19055, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19055, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16512 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42827 q ha hb
    | true =>
      simp only [d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42826 q ha hb
  have h17 (q : Pattern) (ha : d19056 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19057 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16517 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42826 q ha hb
    | true =>
      simp only [d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42828 q ha hb
  have h20 (q : Pattern) (ha : d19058 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d19059 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d19060 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16444 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42826 q ha hb
    | true =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
  have h24 (q : Pattern) (ha : d19061 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d19062 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d16447 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
    | true =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42825 q ha hb
  have h27 (q : Pattern) (ha : d19063 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d19064 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19065 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d19066 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d19067 q = 1) (hb : d180908 q = 1) : d181240 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19067, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19067, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro42834 (p : Pattern) (ha : d19074 p = 1) (hb : d180908 p = 1) : d181245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42830 q ha hb
    | true =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
    | true =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42832 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19070 q = 1) (hb : d180908 q = 1) : d181243 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19070, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19070, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19071 q = 1) (hb : d180908 q = 1) : d181244 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19071, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19071, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16444 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42826 q ha hb
    | true =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
  have h11 (q : Pattern) (ha : d19061 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19062 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16447 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
    | true =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42825 q ha hb
  have h14 (q : Pattern) (ha : d19063 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19064 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19065 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19072 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19073 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19074 q = 1) (hb : d180908 q = 1) : d181245 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19074, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19074, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42835 (p : Pattern) (ha : d19080 p = 1) (hb : d180908 p = 1) : d181251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19068 q = 1) (hb : d180908 q = 1) : d181241 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19068, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42833 q ha hb
    | true =>
      simp only [d19068, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19069 q = 1) (hb : d180908 q = 1) : d181242 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19069, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19069, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19075 q = 1) (hb : d180908 q = 1) : d181246 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42834 q ha hb
    | true =>
      simp only [d19075, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19076 q = 1) (hb : d180908 q = 1) : d181247 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19077 q = 1) (hb : d180908 q = 1) : d181248 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19077, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19077, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19078 q = 1) (hb : d180908 q = 1) : d181249 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19078, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19078, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19079 q = 1) (hb : d180908 q = 1) : d181250 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19079, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19079, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19080 q = 1) (hb : d180908 q = 1) : d181251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19080, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19080, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42836 (p : Pattern) (ha : d19098 p = 1) (hb : d180908 p = 1) : d181265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19075 q = 1) (hb : d180908 q = 1) : d181246 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42834 q ha hb
    | true =>
      simp only [d19075, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19076 q = 1) (hb : d180908 q = 1) : d181247 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42822 q ha hb
    | true =>
      simp only [d19093, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19095 q = 1) (hb : d180908 q = 1) : d181262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19095, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19095, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19096 q = 1) (hb : d180908 q = 1) : d181263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19096, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19096, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19097 q = 1) (hb : d180908 q = 1) : d181264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19097, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19097, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19098 q = 1) (hb : d180908 q = 1) : d181265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19098, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19098, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42837 (p : Pattern) (ha : d12961 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1123 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d12961 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42838 (p : Pattern) (ha : d19174 p = 1) (hb : d180908 p = 1) : d181268 p = 1 := by
  have h0 (q : Pattern) (ha : d19034 q = 1) (hb : d131097 q = 1) : d19034 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19035 q = 1) (hb : d180908 q = 1) : d181221 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19035, d180908, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19036 q = 1) (hb : d180908 q = 1) : d181222 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19036, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19081 q = 1) (hb : d180908 q = 1) : d181252 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19081, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19081, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19174 q = 1) (hb : d180908 q = 1) : d181268 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19174, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19174, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42839 (p : Pattern) (ha : d19184 p = 1) (hb : d180908 p = 1) : d181274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42830 q ha hb
    | true =>
      simp only [d19039, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
    | true =>
      simp only [d19051, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42832 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19175 q = 1) (hb : d180908 q = 1) : d181269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19175, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42820 q ha hb
    | true =>
      simp only [d19175, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42838 q ha hb
  have h9 (q : Pattern) (ha : d19176 q = 1) (hb : d180908 q = 1) : d181270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19176, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19176, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19177 q = 1) (hb : d180908 q = 1) : d181271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19177, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19177, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19178 q = 1) (hb : d180908 q = 1) : d181272 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19178, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19178, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19179 q = 1) (hb : d180908 q = 1) : d181273 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19179, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19179, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16444 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42826 q ha hb
    | true =>
      simp only [d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
  have h14 (q : Pattern) (ha : d19061 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19062 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16447 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
    | true =>
      simp only [d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42825 q ha hb
  have h17 (q : Pattern) (ha : d19063 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19064 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19065 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d16574 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42819 q ha hb
    | true =>
      simp only [d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42837 q ha hb
  have h21 (q : Pattern) (ha : d19180 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19181 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19182 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d19183 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d19184 q = 1) (hb : d180908 q = 1) : d181274 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19184, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19184, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro42840 (p : Pattern) (ha : d19190 p = 1) (hb : d180908 p = 1) : d181280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19185 q = 1) (hb : d180908 q = 1) : d181275 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19185, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42839 q ha hb
    | true =>
      simp only [d19185, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19186 q = 1) (hb : d180908 q = 1) : d181276 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19186, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19186, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19187 q = 1) (hb : d180908 q = 1) : d181277 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19187, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19187, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19188 q = 1) (hb : d180908 q = 1) : d181278 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19188, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19188, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19189 q = 1) (hb : d180908 q = 1) : d181279 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19189, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19189, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19190 q = 1) (hb : d180908 q = 1) : d181280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19190, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19190, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42841 (p : Pattern) (ha : d132662 p = 1) (hb : d180908 p = 1) : d181286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19099 q = 1) (hb : d180908 q = 1) : d181266 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19099, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42835 q ha hb
    | true =>
      simp only [d19099, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42836 q ha hb
  have h2 (q : Pattern) (ha : d132658 q = 1) (hb : d180908 q = 1) : d181267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132658, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132658, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19191 q = 1) (hb : d180908 q = 1) : d181281 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19191, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42840 q ha hb
    | true =>
      simp only [d19191, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19192 q = 1) (hb : d180908 q = 1) : d181282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19192, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19192, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132659 q = 1) (hb : d180908 q = 1) : d181283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132659, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132659, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132660 q = 1) (hb : d180908 q = 1) : d181284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132660, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132660, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132661 q = 1) (hb : d180908 q = 1) : d181285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132661, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132661, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132662 q = 1) (hb : d180908 q = 1) : d181286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132662, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132662, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42842 (p : Pattern) (ha : d132668 p = 1) (hb : d180908 p = 1) : d181303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132663 q = 1) (hb : d180908 q = 1) : d181287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132663, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132663, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42841 q ha hb
  have h2 (q : Pattern) (ha : d19208 q = 1) (hb : d180908 q = 1) : d181298 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19208, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19208, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42824 q ha hb
  have h3 (q : Pattern) (ha : d132664 q = 1) (hb : d180908 q = 1) : d181299 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132664, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132664, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132665 q = 1) (hb : d180908 q = 1) : d181300 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132665, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132665, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132666 q = 1) (hb : d180908 q = 1) : d181301 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132666, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132666, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132667 q = 1) (hb : d180908 q = 1) : d181302 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132667, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132667, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132668 q = 1) (hb : d180908 q = 1) : d181303 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132668, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132668, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42843 (p : Pattern) (ha : d132674 p = 1) (hb : d180908 p = 1) : d181309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132669 q = 1) (hb : d180908 q = 1) : d181304 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132669, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132669, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42842 q ha hb
  have h2 (q : Pattern) (ha : d132670 q = 1) (hb : d180908 q = 1) : d181305 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132670, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132670, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132671 q = 1) (hb : d180908 q = 1) : d181306 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132671, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132671, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132672 q = 1) (hb : d180908 q = 1) : d181307 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132672, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132672, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132673 q = 1) (hb : d180908 q = 1) : d181308 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132673, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132673, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132674 q = 1) (hb : d180908 q = 1) : d181309 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132674, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132674, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42844 (p : Pattern) (ha : d15171 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1584 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15163 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d15164 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d15165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d15171 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42845 (p : Pattern) (ha : d16795 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1572 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10117 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16792 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16792, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16792, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16793 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16794 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15156 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d15157 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d15158 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d16795 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42846 (p : Pattern) (ha : d19270 p = 1) (hb : d180908 p = 1) : d181350 p = 1 := by
  have h0 (q : Pattern) (ha : d19263 q = 1) (hb : d131097 q = 1) : d19263 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19264 q = 1) (hb : d180908 q = 1) : d181345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19264, d180908, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19264, d180908, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19265 q = 1) (hb : d180908 q = 1) : d181346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19265, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19265, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19266 q = 1) (hb : d131097 q = 1) : d19266 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10117 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19267 q = 1) (hb : d180908 q = 1) : d181347 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19267, d180908, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19267, d180908, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19268 q = 1) (hb : d180908 q = 1) : d181348 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19268, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19268, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19269 q = 1) (hb : d180908 q = 1) : d181349 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19269, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19269, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19245 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19246 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19246, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19247 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19247, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19257 q = 1) (hb : d180908 q = 1) : d181339 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19257, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19257, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d19270 q = 1) (hb : d180908 q = 1) : d181350 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19270, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19270, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42847 (p : Pattern) (ha : d19317 p = 1) (hb : d180908 p = 1) : d181381 p = 1 := by
  have h0 (q : Pattern) (ha : d19313 q = 1) (hb : d131097 q = 1) : d19313 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19314 q = 1) (hb : d180908 q = 1) : d181378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19314, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19314, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19315 q = 1) (hb : d180908 q = 1) : d181379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19315, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19315, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19316 q = 1) (hb : d180908 q = 1) : d181380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19316, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19316, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19278 q = 1) (hb : d131097 q = 1) : d19278 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19279 q = 1) (hb : d180908 q = 1) : d181357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19279, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19279, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d19280 q = 1) (hb : d180908 q = 1) : d181358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19280, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19280, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d19281 q = 1) (hb : d180908 q = 1) : d181359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19281, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19281, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19317 q = 1) (hb : d180908 q = 1) : d181381 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19317, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19317, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42848 (p : Pattern) (ha : d19327 p = 1) (hb : d180908 p = 1) : d181387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19318 q = 1) (hb : d180908 q = 1) : d181382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19318, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
    | true =>
      simp only [d19318, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42847 q ha hb
  have h2 (q : Pattern) (ha : d19319 q = 1) (hb : d180908 q = 1) : d181383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19319, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19319, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19320 q = 1) (hb : d180908 q = 1) : d181384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19320, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19320, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19321 q = 1) (hb : d180908 q = 1) : d181385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19321, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19321, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19322 q = 1) (hb : d180908 q = 1) : d181386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19322, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19322, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16803 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
    | true =>
      simp only [d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42844 q ha hb
  have h7 (q : Pattern) (ha : d19323 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19324 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19325 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19326 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19327 q = 1) (hb : d180908 q = 1) : d181387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19327, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19327, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42849 (p : Pattern) (ha : d19439 p = 1) (hb : d180908 p = 1) : d181419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19328 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42848 q ha hb
    | true =>
      simp only [d19328, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19329 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19436 q = 1) (hb : d180908 q = 1) : d181416 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19436, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19436, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19437 q = 1) (hb : d180908 q = 1) : d181417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19437, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19437, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19438 q = 1) (hb : d180908 q = 1) : d181418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19438, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19438, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19439 q = 1) (hb : d180908 q = 1) : d181419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19439, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19439, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42850 (p : Pattern) (ha : d19445 p = 1) (hb : d180908 p = 1) : d181425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19440 q = 1) (hb : d180908 q = 1) : d181420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19440, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42849 q ha hb
    | true =>
      simp only [d19440, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19441 q = 1) (hb : d180908 q = 1) : d181421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19441, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19441, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19442 q = 1) (hb : d180908 q = 1) : d181422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19442, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19442, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19443 q = 1) (hb : d180908 q = 1) : d181423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19443, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19443, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19444 q = 1) (hb : d180908 q = 1) : d181424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19444, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19444, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19445 q = 1) (hb : d180908 q = 1) : d181425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19445, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19445, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42851 (p : Pattern) (ha : d15166 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5136 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5136, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5136, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5137 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5138 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15163 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d15164 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d15165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d15166 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42852 (p : Pattern) (ha : d16791 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1557 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16787 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16787, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16787, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16788 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16789 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15151 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d15152 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15156 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d15157 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d16790 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16791 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42853 (p : Pattern) (ha : d16863 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1667 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10038 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d16859 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d16860 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16861 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10048 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15229 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15229, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d15230 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15151 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15151, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15151, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d15152 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d16862 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16863 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42854 (p : Pattern) (ha : d16868 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13348 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13348, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13349 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15156 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15157 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d16867 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15158 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d16868 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42855 (p : Pattern) (ha : d19237 p = 1) (hb : d180908 p = 1) : d181323 p = 1 := by
  have h0 (q : Pattern) (ha : d19223 q = 1) (hb : d131097 q = 1) : d19223 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19224 q = 1) (hb : d180908 q = 1) : d181313 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19224, d180908, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19224, d180908, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19225 q = 1) (hb : d180908 q = 1) : d181314 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19225, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19225, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19226 q = 1) (hb : d131097 q = 1) : d19226 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10038 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19227 q = 1) (hb : d180908 q = 1) : d181315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19227, d180908, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19227, d180908, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19228 q = 1) (hb : d180908 q = 1) : d181316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19228, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19228, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19229 q = 1) (hb : d180908 q = 1) : d181317 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19229, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19229, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19230 q = 1) (hb : d131097 q = 1) : d19230 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10048 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19231 q = 1) (hb : d180908 q = 1) : d181318 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19231, d180908, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19231, d180908, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19232 q = 1) (hb : d180908 q = 1) : d181319 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19232, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19232, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19233 q = 1) (hb : d131097 q = 1) : d19233 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19234 q = 1) (hb : d180908 q = 1) : d181320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19234, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19234, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d19235 q = 1) (hb : d180908 q = 1) : d181321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19235, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19235, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19236 q = 1) (hb : d180908 q = 1) : d181322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19236, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19236, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19237 q = 1) (hb : d180908 q = 1) : d181323 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19237, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19237, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42856 (p : Pattern) (ha : d19249 p = 1) (hb : d180908 p = 1) : d181332 p = 1 := by
  have h0 (q : Pattern) (ha : d19238 q = 1) (hb : d131097 q = 1) : d19238 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19239 q = 1) (hb : d180908 q = 1) : d181324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19239, d180908, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19239, d180908, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19240 q = 1) (hb : d180908 q = 1) : d181325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19240, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19240, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19241 q = 1) (hb : d131097 q = 1) : d19241 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19242 q = 1) (hb : d180908 q = 1) : d181326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19242, d180908, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19242, d180908, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19243 q = 1) (hb : d180908 q = 1) : d181327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19243, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19243, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19244 q = 1) (hb : d180908 q = 1) : d181328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19244, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19244, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19233 q = 1) (hb : d131097 q = 1) : d19233 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10065 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19234 q = 1) (hb : d180908 q = 1) : d181320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19234, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19234, d180908, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19235 q = 1) (hb : d180908 q = 1) : d181321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19235, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19235, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19245 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19246 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19246, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d19247 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19247, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19248 q = 1) (hb : d180908 q = 1) : d181331 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19248, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19248, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19249 q = 1) (hb : d180908 q = 1) : d181332 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19249, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19249, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42857 (p : Pattern) (ha : d19258 p = 1) (hb : d180908 p = 1) : d181340 p = 1 := by
  have h0 (q : Pattern) (ha : d19253 q = 1) (hb : d131097 q = 1) : d19253 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19254 q = 1) (hb : d180908 q = 1) : d181336 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19254, d180908, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19254, d180908, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19255 q = 1) (hb : d180908 q = 1) : d181337 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19255, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19255, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19245 q = 1) (hb : d131097 q = 1) : d19245 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10087 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19246 q = 1) (hb : d180908 q = 1) : d181329 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19246, d180908, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19247 q = 1) (hb : d180908 q = 1) : d181330 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19247, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19256 q = 1) (hb : d180908 q = 1) : d181338 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19256, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19256, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19257 q = 1) (hb : d180908 q = 1) : d181339 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19257, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19257, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19258 q = 1) (hb : d180908 q = 1) : d181340 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19258, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19258, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42858 (p : Pattern) (ha : d19282 p = 1) (hb : d180908 p = 1) : d181360 p = 1 := by
  have h0 (q : Pattern) (ha : d19274 q = 1) (hb : d131097 q = 1) : d19274 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5135 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19275 q = 1) (hb : d180908 q = 1) : d181354 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19275, d180908, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19275, d180908, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19276 q = 1) (hb : d180908 q = 1) : d181355 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19276, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19276, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19277 q = 1) (hb : d180908 q = 1) : d181356 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19277, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19277, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19278 q = 1) (hb : d131097 q = 1) : d19278 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10137 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19279 q = 1) (hb : d180908 q = 1) : d181357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19279, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19279, d180908, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d19280 q = 1) (hb : d180908 q = 1) : d181358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19280, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19280, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d19281 q = 1) (hb : d180908 q = 1) : d181359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19281, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19281, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19282 q = 1) (hb : d180908 q = 1) : d181360 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19282, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19282, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42859 (p : Pattern) (ha : d19299 p = 1) (hb : d180908 p = 1) : d181366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19250 q = 1) (hb : d180908 q = 1) : d181333 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19250, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42855 q ha hb
    | true =>
      simp only [d19250, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42856 q ha hb
  have h2 (q : Pattern) (ha : d19251 q = 1) (hb : d180908 q = 1) : d181334 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19251, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19251, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19252 q = 1) (hb : d180908 q = 1) : d181335 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19252, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19252, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19259 q = 1) (hb : d180908 q = 1) : d181341 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19259, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42856 q ha hb
    | true =>
      simp only [d19259, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42857 q ha hb
  have h5 (q : Pattern) (ha : d19260 q = 1) (hb : d180908 q = 1) : d181342 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19260, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19260, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19261 q = 1) (hb : d180908 q = 1) : d181343 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19261, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19261, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19262 q = 1) (hb : d180908 q = 1) : d181344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19262, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19262, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19271 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42856 q ha hb
    | true =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
  have h9 (q : Pattern) (ha : d19272 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19273 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19283 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
    | true =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42858 q ha hb
  have h12 (q : Pattern) (ha : d19284 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19285 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19286 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19287 q = 1) (hb : d180908 q = 1) : d181365 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19287, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19287, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16864 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42853 q ha hb
    | true =>
      simp only [d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42852 q ha hb
  have h17 (q : Pattern) (ha : d19288 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19289 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16869 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42852 q ha hb
    | true =>
      simp only [d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42854 q ha hb
  have h20 (q : Pattern) (ha : d19290 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d19291 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d19292 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d16796 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42852 q ha hb
    | true =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
  have h24 (q : Pattern) (ha : d19293 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d19294 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d16799 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
    | true =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42851 q ha hb
  have h27 (q : Pattern) (ha : d19295 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d19296 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19297 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d19298 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d19299 q = 1) (hb : d180908 q = 1) : d181366 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19299, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19299, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro42860 (p : Pattern) (ha : d19306 p = 1) (hb : d180908 p = 1) : d181371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42856 q ha hb
    | true =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
    | true =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42858 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19302 q = 1) (hb : d180908 q = 1) : d181369 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19302, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19302, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19303 q = 1) (hb : d180908 q = 1) : d181370 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19303, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19303, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16796 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42852 q ha hb
    | true =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
  have h11 (q : Pattern) (ha : d19293 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19294 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16799 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
    | true =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42851 q ha hb
  have h14 (q : Pattern) (ha : d19295 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19296 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19297 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19304 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19305 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19306 q = 1) (hb : d180908 q = 1) : d181371 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19306, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19306, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42861 (p : Pattern) (ha : d19312 p = 1) (hb : d180908 p = 1) : d181377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19300 q = 1) (hb : d180908 q = 1) : d181367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19300, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42859 q ha hb
    | true =>
      simp only [d19300, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19301 q = 1) (hb : d180908 q = 1) : d181368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19301, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19301, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19307 q = 1) (hb : d180908 q = 1) : d181372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42860 q ha hb
    | true =>
      simp only [d19307, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19308 q = 1) (hb : d180908 q = 1) : d181373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19309 q = 1) (hb : d180908 q = 1) : d181374 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19309, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19309, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19310 q = 1) (hb : d180908 q = 1) : d181375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19310, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19310, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19311 q = 1) (hb : d180908 q = 1) : d181376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19311, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19311, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19312 q = 1) (hb : d180908 q = 1) : d181377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19312, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19312, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42862 (p : Pattern) (ha : d19333 p = 1) (hb : d180908 p = 1) : d181393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19307 q = 1) (hb : d180908 q = 1) : d181372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42860 q ha hb
    | true =>
      simp only [d19307, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19308 q = 1) (hb : d180908 q = 1) : d181373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19328 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42848 q ha hb
    | true =>
      simp only [d19328, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19329 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19330 q = 1) (hb : d180908 q = 1) : d181390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19330, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19330, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19331 q = 1) (hb : d180908 q = 1) : d181391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19331, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19331, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19332 q = 1) (hb : d180908 q = 1) : d181392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19332, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19332, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19333 q = 1) (hb : d180908 q = 1) : d181393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19333, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19333, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42863 (p : Pattern) (ha : d13287 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1584 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d13287 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42864 (p : Pattern) (ha : d19412 p = 1) (hb : d180908 p = 1) : d181396 p = 1 := by
  have h0 (q : Pattern) (ha : d19313 q = 1) (hb : d131097 q = 1) : d19313 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1583 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19314 q = 1) (hb : d180908 q = 1) : d181378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19314, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19314, d180908, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19315 q = 1) (hb : d180908 q = 1) : d181379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19315, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19315, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19316 q = 1) (hb : d180908 q = 1) : d181380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19316, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19316, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19412 q = 1) (hb : d180908 q = 1) : d181396 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19412, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19412, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42865 (p : Pattern) (ha : d19422 p = 1) (hb : d180908 p = 1) : d181402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42856 q ha hb
    | true =>
      simp only [d19271, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
    | true =>
      simp only [d19283, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42858 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19413 q = 1) (hb : d180908 q = 1) : d181397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19413, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42846 q ha hb
    | true =>
      simp only [d19413, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42864 q ha hb
  have h9 (q : Pattern) (ha : d19414 q = 1) (hb : d180908 q = 1) : d181398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19414, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19414, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19415 q = 1) (hb : d180908 q = 1) : d181399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19415, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19415, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19416 q = 1) (hb : d180908 q = 1) : d181400 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19416, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19416, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19417 q = 1) (hb : d180908 q = 1) : d181401 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19417, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19417, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16796 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42852 q ha hb
    | true =>
      simp only [d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
  have h14 (q : Pattern) (ha : d19293 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19294 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16799 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
    | true =>
      simp only [d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42851 q ha hb
  have h17 (q : Pattern) (ha : d19295 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19296 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19297 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d16929 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42845 q ha hb
    | true =>
      simp only [d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42863 q ha hb
  have h21 (q : Pattern) (ha : d19418 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19419 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19420 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d19421 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d19422 q = 1) (hb : d180908 q = 1) : d181402 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19422, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19422, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro42866 (p : Pattern) (ha : d19428 p = 1) (hb : d180908 p = 1) : d181408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19423 q = 1) (hb : d180908 q = 1) : d181403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19423, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42865 q ha hb
    | true =>
      simp only [d19423, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19424 q = 1) (hb : d180908 q = 1) : d181404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19424, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19424, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19425 q = 1) (hb : d180908 q = 1) : d181405 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19425, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19425, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19426 q = 1) (hb : d180908 q = 1) : d181406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19426, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19426, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19427 q = 1) (hb : d180908 q = 1) : d181407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19427, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19427, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19428 q = 1) (hb : d180908 q = 1) : d181408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19428, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19428, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42867 (p : Pattern) (ha : d132682 p = 1) (hb : d180908 p = 1) : d181414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19334 q = 1) (hb : d180908 q = 1) : d181394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19334, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42861 q ha hb
    | true =>
      simp only [d19334, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42862 q ha hb
  have h2 (q : Pattern) (ha : d132678 q = 1) (hb : d180908 q = 1) : d181395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132678, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132678, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19429 q = 1) (hb : d180908 q = 1) : d181409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19429, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42866 q ha hb
    | true =>
      simp only [d19429, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19430 q = 1) (hb : d180908 q = 1) : d181410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19430, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19430, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132679 q = 1) (hb : d180908 q = 1) : d181411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132679, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132679, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132680 q = 1) (hb : d180908 q = 1) : d181412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132680, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132680, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132681 q = 1) (hb : d180908 q = 1) : d181413 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132681, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132681, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132682 q = 1) (hb : d180908 q = 1) : d181414 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132682, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132682, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42868 (p : Pattern) (ha : d132688 p = 1) (hb : d180908 p = 1) : d181431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132683 q = 1) (hb : d180908 q = 1) : d181415 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132683, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132683, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42867 q ha hb
  have h2 (q : Pattern) (ha : d19446 q = 1) (hb : d180908 q = 1) : d181426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19446, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19446, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42850 q ha hb
  have h3 (q : Pattern) (ha : d132684 q = 1) (hb : d180908 q = 1) : d181427 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132684, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132684, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132685 q = 1) (hb : d180908 q = 1) : d181428 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132685, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132685, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132686 q = 1) (hb : d180908 q = 1) : d181429 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132686, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132686, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132687 q = 1) (hb : d180908 q = 1) : d181430 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132687, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132687, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132688 q = 1) (hb : d180908 q = 1) : d181431 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132688, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132688, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42869 (p : Pattern) (ha : d132694 p = 1) (hb : d180908 p = 1) : d181437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132689 q = 1) (hb : d180908 q = 1) : d181432 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132689, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132689, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42868 q ha hb
  have h2 (q : Pattern) (ha : d132690 q = 1) (hb : d180908 q = 1) : d181433 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132690, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132690, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132691 q = 1) (hb : d180908 q = 1) : d181434 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132691, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132691, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132692 q = 1) (hb : d180908 q = 1) : d181435 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132692, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132692, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132693 q = 1) (hb : d180908 q = 1) : d181436 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132693, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132693, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132694 q = 1) (hb : d180908 q = 1) : d181437 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132694, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132694, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42870 (p : Pattern) (ha : d15563 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2067 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15555 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d15556 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d15557 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d15563 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42871 (p : Pattern) (ha : d17161 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2054 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2055 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10393 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17158 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17158, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17159 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d17160 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15548 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d15549 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d15550 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d17161 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42872 (p : Pattern) (ha : d19502 p = 1) (hb : d180908 p = 1) : d181474 p = 1 := by
  have h0 (q : Pattern) (ha : d19495 q = 1) (hb : d131097 q = 1) : d19495 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2054 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19496 q = 1) (hb : d180908 q = 1) : d181469 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19496, d180908, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19496, d180908, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19497 q = 1) (hb : d180908 q = 1) : d181470 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19497, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19497, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19498 q = 1) (hb : d131097 q = 1) : d19498 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10393 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19499 q = 1) (hb : d180908 q = 1) : d181471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19499, d180908, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19499, d180908, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19500 q = 1) (hb : d180908 q = 1) : d181472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19500, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19500, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19501 q = 1) (hb : d180908 q = 1) : d181473 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19501, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19501, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19481 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19482 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19482, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19483 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19483, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19489 q = 1) (hb : d180908 q = 1) : d181463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19489, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19489, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d19502 q = 1) (hb : d180908 q = 1) : d181474 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19502, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19502, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42873 (p : Pattern) (ha : d19549 p = 1) (hb : d180908 p = 1) : d181505 p = 1 := by
  have h0 (q : Pattern) (ha : d19545 q = 1) (hb : d131097 q = 1) : d19545 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19546 q = 1) (hb : d180908 q = 1) : d181502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19546, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19546, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19547 q = 1) (hb : d180908 q = 1) : d181503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19547, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19547, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19548 q = 1) (hb : d180908 q = 1) : d181504 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19548, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19548, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19510 q = 1) (hb : d131097 q = 1) : d19510 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19511 q = 1) (hb : d180908 q = 1) : d181481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19511, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19511, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d19512 q = 1) (hb : d180908 q = 1) : d181482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19512, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19512, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d19513 q = 1) (hb : d180908 q = 1) : d181483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19513, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19513, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19549 q = 1) (hb : d180908 q = 1) : d181505 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19549, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19549, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42874 (p : Pattern) (ha : d19559 p = 1) (hb : d180908 p = 1) : d181511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19550 q = 1) (hb : d180908 q = 1) : d181506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19550, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
    | true =>
      simp only [d19550, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42873 q ha hb
  have h2 (q : Pattern) (ha : d19551 q = 1) (hb : d180908 q = 1) : d181507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19551, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19552 q = 1) (hb : d180908 q = 1) : d181508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19553 q = 1) (hb : d180908 q = 1) : d181509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19553, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19554 q = 1) (hb : d180908 q = 1) : d181510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19554, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19554, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17169 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
    | true =>
      simp only [d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42870 q ha hb
  have h7 (q : Pattern) (ha : d19555 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19556 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19557 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19558 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19559 q = 1) (hb : d180908 q = 1) : d181511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19559, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19559, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42875 (p : Pattern) (ha : d19671 p = 1) (hb : d180908 p = 1) : d181543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19560 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42874 q ha hb
    | true =>
      simp only [d19560, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19561 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19668 q = 1) (hb : d180908 q = 1) : d181540 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19668, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19668, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19669 q = 1) (hb : d180908 q = 1) : d181541 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19669, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19669, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19670 q = 1) (hb : d180908 q = 1) : d181542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19670, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19670, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19671 q = 1) (hb : d180908 q = 1) : d181543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19671, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19671, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42876 (p : Pattern) (ha : d19677 p = 1) (hb : d180908 p = 1) : d181549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19672 q = 1) (hb : d180908 q = 1) : d181544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19672, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42875 q ha hb
    | true =>
      simp only [d19672, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19673 q = 1) (hb : d180908 q = 1) : d181545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19673, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19673, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19674 q = 1) (hb : d180908 q = 1) : d181546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19674, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19674, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19675 q = 1) (hb : d180908 q = 1) : d181547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19675, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19675, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19676 q = 1) (hb : d180908 q = 1) : d181548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19676, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19676, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19677 q = 1) (hb : d180908 q = 1) : d181549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19677, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19677, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42877 (p : Pattern) (ha : d15558 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5248 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5249 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5249, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5249, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5250 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5251 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15555 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d15556 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d15557 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d15558 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42878 (p : Pattern) (ha : d17157 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2037 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10366 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17153 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17154 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d17155 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13675 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d13676 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15548 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d15549 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d17156 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17157 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro42879 (p : Pattern) (ha : d17229 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2146 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10345 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17225 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d17226 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d17227 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13675 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d13676 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d17228 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17229 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42880 (p : Pattern) (ha : d17233 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13675 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15548 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15549 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d17156 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15550 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d17233 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro42881 (p : Pattern) (ha : d19473 p = 1) (hb : d180908 p = 1) : d181450 p = 1 := by
  have h0 (q : Pattern) (ha : d19462 q = 1) (hb : d131097 q = 1) : d19462 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19463 q = 1) (hb : d180908 q = 1) : d181442 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19463, d180908, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19463, d180908, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19464 q = 1) (hb : d180908 q = 1) : d181443 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19464, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19464, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19465 q = 1) (hb : d131097 q = 1) : d19465 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10345 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19466 q = 1) (hb : d180908 q = 1) : d181444 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19466, d180908, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19466, d180908, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19467 q = 1) (hb : d180908 q = 1) : d181445 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19467, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19467, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19468 q = 1) (hb : d180908 q = 1) : d181446 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19468, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19468, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19469 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19470 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19470, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19471 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19471, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19472 q = 1) (hb : d180908 q = 1) : d181449 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19472, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19472, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19473 q = 1) (hb : d180908 q = 1) : d181450 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19473, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19473, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42882 (p : Pattern) (ha : d19485 p = 1) (hb : d180908 p = 1) : d181459 p = 1 := by
  have h0 (q : Pattern) (ha : d19474 q = 1) (hb : d131097 q = 1) : d19474 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19475 q = 1) (hb : d180908 q = 1) : d181451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19475, d180908, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19475, d180908, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19476 q = 1) (hb : d180908 q = 1) : d181452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19476, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19476, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19477 q = 1) (hb : d131097 q = 1) : d19477 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10366 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19478 q = 1) (hb : d180908 q = 1) : d181453 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19478, d180908, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19478, d180908, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19479 q = 1) (hb : d180908 q = 1) : d181454 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19479, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19479, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19480 q = 1) (hb : d180908 q = 1) : d181455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19480, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19480, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19469 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19470 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19470, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d19471 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19471, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d19481 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19482 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19482, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d19483 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19483, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d19484 q = 1) (hb : d180908 q = 1) : d181458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19484, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19484, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19485 q = 1) (hb : d180908 q = 1) : d181459 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19485, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19485, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42883 (p : Pattern) (ha : d19490 p = 1) (hb : d180908 p = 1) : d181464 p = 1 := by
  have h0 (q : Pattern) (ha : d19469 q = 1) (hb : d131097 q = 1) : d19469 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19470 q = 1) (hb : d180908 q = 1) : d181447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19470, d180908, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19471 q = 1) (hb : d180908 q = 1) : d181448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19471, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19481 q = 1) (hb : d131097 q = 1) : d19481 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10373 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19482 q = 1) (hb : d180908 q = 1) : d181456 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19482, d180908, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d19483 q = 1) (hb : d180908 q = 1) : d181457 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19483, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d19484 q = 1) (hb : d180908 q = 1) : d181458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19484, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19484, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19489 q = 1) (hb : d180908 q = 1) : d181463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19489, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19489, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19490 q = 1) (hb : d180908 q = 1) : d181464 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19490, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19490, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42884 (p : Pattern) (ha : d19514 p = 1) (hb : d180908 p = 1) : d181484 p = 1 := by
  have h0 (q : Pattern) (ha : d19506 q = 1) (hb : d131097 q = 1) : d19506 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5248 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19507 q = 1) (hb : d180908 q = 1) : d181478 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19507, d180908, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19507, d180908, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19508 q = 1) (hb : d180908 q = 1) : d181479 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19508, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19508, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19509 q = 1) (hb : d180908 q = 1) : d181480 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19509, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19509, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19510 q = 1) (hb : d131097 q = 1) : d19510 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d10414 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19511 q = 1) (hb : d180908 q = 1) : d181481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19511, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19511, d180908, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d19512 q = 1) (hb : d180908 q = 1) : d181482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19512, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19512, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d19513 q = 1) (hb : d180908 q = 1) : d181483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19513, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19513, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d19514 q = 1) (hb : d180908 q = 1) : d181484 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19514, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19514, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42885 (p : Pattern) (ha : d19531 p = 1) (hb : d180908 p = 1) : d181490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19486 q = 1) (hb : d180908 q = 1) : d181460 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19486, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42881 q ha hb
    | true =>
      simp only [d19486, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42882 q ha hb
  have h2 (q : Pattern) (ha : d19487 q = 1) (hb : d180908 q = 1) : d181461 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19487, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19487, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19488 q = 1) (hb : d180908 q = 1) : d181462 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19488, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19488, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19491 q = 1) (hb : d180908 q = 1) : d181465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19491, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42882 q ha hb
    | true =>
      simp only [d19491, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42883 q ha hb
  have h5 (q : Pattern) (ha : d19492 q = 1) (hb : d180908 q = 1) : d181466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19492, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19492, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19493 q = 1) (hb : d180908 q = 1) : d181467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19493, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19493, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19494 q = 1) (hb : d180908 q = 1) : d181468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19494, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19494, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19503 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42882 q ha hb
    | true =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
  have h9 (q : Pattern) (ha : d19504 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19505 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19515 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
    | true =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42884 q ha hb
  have h12 (q : Pattern) (ha : d19516 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19517 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19518 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19519 q = 1) (hb : d180908 q = 1) : d181489 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19519, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19519, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17230 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42879 q ha hb
    | true =>
      simp only [d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42878 q ha hb
  have h17 (q : Pattern) (ha : d19520 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19521 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d17234 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42878 q ha hb
    | true =>
      simp only [d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42880 q ha hb
  have h20 (q : Pattern) (ha : d19522 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d19523 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d19524 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d17162 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42878 q ha hb
    | true =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
  have h24 (q : Pattern) (ha : d19525 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d19526 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d17165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
    | true =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42877 q ha hb
  have h27 (q : Pattern) (ha : d19527 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d19528 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19529 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d19530 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d19531 q = 1) (hb : d180908 q = 1) : d181490 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19531, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19531, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro42886 (p : Pattern) (ha : d19538 p = 1) (hb : d180908 p = 1) : d181495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42882 q ha hb
    | true =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
    | true =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42884 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19534 q = 1) (hb : d180908 q = 1) : d181493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19534, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19534, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19535 q = 1) (hb : d180908 q = 1) : d181494 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19535, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19535, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17162 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42878 q ha hb
    | true =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
  have h11 (q : Pattern) (ha : d19525 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19526 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
    | true =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42877 q ha hb
  have h14 (q : Pattern) (ha : d19527 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19528 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19529 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19536 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19537 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19538 q = 1) (hb : d180908 q = 1) : d181495 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19538, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19538, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro42887 (p : Pattern) (ha : d19544 p = 1) (hb : d180908 p = 1) : d181501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19532 q = 1) (hb : d180908 q = 1) : d181491 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19532, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42885 q ha hb
    | true =>
      simp only [d19532, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19533 q = 1) (hb : d180908 q = 1) : d181492 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19533, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19533, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19539 q = 1) (hb : d180908 q = 1) : d181496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42886 q ha hb
    | true =>
      simp only [d19539, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19540 q = 1) (hb : d180908 q = 1) : d181497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19541 q = 1) (hb : d180908 q = 1) : d181498 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19541, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19541, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19542 q = 1) (hb : d180908 q = 1) : d181499 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19542, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19542, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19543 q = 1) (hb : d180908 q = 1) : d181500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19543, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19543, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19544 q = 1) (hb : d180908 q = 1) : d181501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19544, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19544, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42888 (p : Pattern) (ha : d19565 p = 1) (hb : d180908 p = 1) : d181517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19539 q = 1) (hb : d180908 q = 1) : d181496 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42886 q ha hb
    | true =>
      simp only [d19539, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19540 q = 1) (hb : d180908 q = 1) : d181497 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42874 q ha hb
    | true =>
      simp only [d19560, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19562 q = 1) (hb : d180908 q = 1) : d181514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19562, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19562, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19563 q = 1) (hb : d180908 q = 1) : d181515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19563, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19563, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19564 q = 1) (hb : d180908 q = 1) : d181516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19564, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19564, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19565 q = 1) (hb : d180908 q = 1) : d181517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19565, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19565, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42889 (p : Pattern) (ha : d13614 p = 1) (hb : d180908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131097 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2067 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d180908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d13614 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42890 (p : Pattern) (ha : d19644 p = 1) (hb : d180908 p = 1) : d181520 p = 1 := by
  have h0 (q : Pattern) (ha : d19545 q = 1) (hb : d131097 q = 1) : d19545 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19546 q = 1) (hb : d180908 q = 1) : d181502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19546, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19546, d180908, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19547 q = 1) (hb : d180908 q = 1) : d181503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19547, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19547, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19548 q = 1) (hb : d180908 q = 1) : d181504 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19548, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19548, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d19644 q = 1) (hb : d180908 q = 1) : d181520 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19644, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19644, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro42891 (p : Pattern) (ha : d19654 p = 1) (hb : d180908 p = 1) : d181526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42882 q ha hb
    | true =>
      simp only [d19503, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
    | true =>
      simp only [d19515, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42884 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19645 q = 1) (hb : d180908 q = 1) : d181521 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19645, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42872 q ha hb
    | true =>
      simp only [d19645, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42890 q ha hb
  have h9 (q : Pattern) (ha : d19646 q = 1) (hb : d180908 q = 1) : d181522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19646, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19646, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19647 q = 1) (hb : d180908 q = 1) : d181523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19647, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19647, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19648 q = 1) (hb : d180908 q = 1) : d181524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19648, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19648, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19649 q = 1) (hb : d180908 q = 1) : d181525 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19649, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19649, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17162 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42878 q ha hb
    | true =>
      simp only [d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
  have h14 (q : Pattern) (ha : d19525 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19526 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17165 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
    | true =>
      simp only [d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42877 q ha hb
  have h17 (q : Pattern) (ha : d19527 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19528 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19529 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d17294 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42871 q ha hb
    | true =>
      simp only [d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42889 q ha hb
  have h21 (q : Pattern) (ha : d19650 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19651 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19652 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d19653 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d19654 q = 1) (hb : d180908 q = 1) : d181526 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19654, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19654, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro42892 (p : Pattern) (ha : d19660 p = 1) (hb : d180908 p = 1) : d181532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19655 q = 1) (hb : d180908 q = 1) : d181527 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19655, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42891 q ha hb
    | true =>
      simp only [d19655, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19656 q = 1) (hb : d180908 q = 1) : d181528 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19656, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19656, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19657 q = 1) (hb : d180908 q = 1) : d181529 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19657, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19657, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19658 q = 1) (hb : d180908 q = 1) : d181530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19658, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19658, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19659 q = 1) (hb : d180908 q = 1) : d181531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19659, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19659, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19660 q = 1) (hb : d180908 q = 1) : d181532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19660, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19660, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42893 (p : Pattern) (ha : d132703 p = 1) (hb : d180908 p = 1) : d181538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19566 q = 1) (hb : d180908 q = 1) : d181518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19566, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42887 q ha hb
    | true =>
      simp only [d19566, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42888 q ha hb
  have h2 (q : Pattern) (ha : d132699 q = 1) (hb : d180908 q = 1) : d181519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132699, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132699, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19661 q = 1) (hb : d180908 q = 1) : d181533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19661, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42892 q ha hb
    | true =>
      simp only [d19661, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19662 q = 1) (hb : d180908 q = 1) : d181534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19662, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19662, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132700 q = 1) (hb : d180908 q = 1) : d181535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132700, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132700, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132701 q = 1) (hb : d180908 q = 1) : d181536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132701, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132701, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132702 q = 1) (hb : d180908 q = 1) : d181537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132702, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132702, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132703 q = 1) (hb : d180908 q = 1) : d181538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132703, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132703, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42894 (p : Pattern) (ha : d132709 p = 1) (hb : d180908 p = 1) : d181555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132704 q = 1) (hb : d180908 q = 1) : d181539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132704, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132704, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42893 q ha hb
  have h2 (q : Pattern) (ha : d19678 q = 1) (hb : d180908 q = 1) : d181550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19678, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19678, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42876 q ha hb
  have h3 (q : Pattern) (ha : d132705 q = 1) (hb : d180908 q = 1) : d181551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132705, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132705, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132706 q = 1) (hb : d180908 q = 1) : d181552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132706, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132706, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132707 q = 1) (hb : d180908 q = 1) : d181553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132707, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132707, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132708 q = 1) (hb : d180908 q = 1) : d181554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132708, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132708, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132709 q = 1) (hb : d180908 q = 1) : d181555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132709, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132709, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42895 (p : Pattern) (ha : d132715 p = 1) (hb : d180908 p = 1) : d181561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132710 q = 1) (hb : d180908 q = 1) : d181556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132710, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132710, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42894 q ha hb
  have h2 (q : Pattern) (ha : d132711 q = 1) (hb : d180908 q = 1) : d181557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132711, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132711, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132712 q = 1) (hb : d180908 q = 1) : d181558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132712, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132712, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132713 q = 1) (hb : d180908 q = 1) : d181559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132713, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132713, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132714 q = 1) (hb : d180908 q = 1) : d181560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132714, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132714, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132715 q = 1) (hb : d180908 q = 1) : d181561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132715, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132715, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42896 (p : Pattern) (ha : d132721 p = 1) (hb : d180908 p = 1) : d181567 p = 1 := by
  have h0 (q : Pattern) (ha : d132638 q = 1) (hb : d180908 q = 1) : d181096 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132638, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42781 q ha hb
    | true =>
      simp only [d132638, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42796 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132656 q = 1) (hb : d180908 q = 1) : d181185 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132656, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132656, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42817 q ha hb
  have h3 (q : Pattern) (ha : d132657 q = 1) (hb : d180908 q = 1) : d181186 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132657, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132657, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132675 q = 1) (hb : d180908 q = 1) : d181310 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132675, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132675, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42843 q ha hb
  have h5 (q : Pattern) (ha : d132676 q = 1) (hb : d180908 q = 1) : d181311 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132676, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132676, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132677 q = 1) (hb : d180908 q = 1) : d181312 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132677, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132677, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132695 q = 1) (hb : d180908 q = 1) : d181438 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132695, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132695, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42869 q ha hb
  have h8 (q : Pattern) (ha : d132696 q = 1) (hb : d180908 q = 1) : d181439 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132696, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132696, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132697 q = 1) (hb : d180908 q = 1) : d181440 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132697, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132697, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132698 q = 1) (hb : d180908 q = 1) : d181441 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132698, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132698, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d132716 q = 1) (hb : d180908 q = 1) : d181562 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132716, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132716, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42895 q ha hb
  have h12 (q : Pattern) (ha : d132717 q = 1) (hb : d180908 q = 1) : d181563 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132717, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132717, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d132718 q = 1) (hb : d180908 q = 1) : d181564 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132718, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132718, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d132719 q = 1) (hb : d180908 q = 1) : d181565 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132719, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132719, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d132720 q = 1) (hb : d180908 q = 1) : d181566 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d132720, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d132720, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d132721 q = 1) (hb : d180908 q = 1) : d181567 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d132721, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d132721, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro42897 (p : Pattern) (ha : d132727 p = 1) (hb : d180908 p = 1) : d181573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132722 q = 1) (hb : d180908 q = 1) : d181568 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d132722, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42896 q ha hb
    | true =>
      simp only [d132722, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132723 q = 1) (hb : d180908 q = 1) : d181569 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d132723, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132723, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132724 q = 1) (hb : d180908 q = 1) : d181570 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d132724, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132724, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132725 q = 1) (hb : d180908 q = 1) : d181571 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d132725, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132725, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132726 q = 1) (hb : d180908 q = 1) : d181572 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d132726, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132726, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132727 q = 1) (hb : d180908 q = 1) : d181573 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d132727, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132727, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42898 (p : Pattern) (ha : d132733 p = 1) (hb : d180908 p = 1) : d181579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132728 q = 1) (hb : d180908 q = 1) : d181574 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d132728, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42897 q ha hb
    | true =>
      simp only [d132728, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132729 q = 1) (hb : d180908 q = 1) : d181575 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d132729, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132729, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132730 q = 1) (hb : d180908 q = 1) : d181576 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d132730, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132730, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132731 q = 1) (hb : d180908 q = 1) : d181577 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d132731, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132731, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132732 q = 1) (hb : d180908 q = 1) : d181578 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d132732, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132732, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132733 q = 1) (hb : d180908 q = 1) : d181579 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d132733, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132733, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42899 (p : Pattern) (ha : d132739 p = 1) (hb : d180908 p = 1) : d181585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132734 q = 1) (hb : d180908 q = 1) : d181580 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d132734, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42898 q ha hb
    | true =>
      simp only [d132734, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132735 q = 1) (hb : d180908 q = 1) : d181581 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d132735, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132735, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132736 q = 1) (hb : d180908 q = 1) : d181582 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d132736, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132736, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132737 q = 1) (hb : d180908 q = 1) : d181583 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d132737, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132737, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132738 q = 1) (hb : d180908 q = 1) : d181584 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d132738, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132738, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132739 q = 1) (hb : d180908 q = 1) : d181585 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d132739, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132739, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42900 (p : Pattern) (ha : d132745 p = 1) (hb : d180908 p = 1) : d181591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132740 q = 1) (hb : d180908 q = 1) : d181586 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d132740, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42899 q ha hb
    | true =>
      simp only [d132740, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132741 q = 1) (hb : d180908 q = 1) : d181587 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d132741, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132741, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132742 q = 1) (hb : d180908 q = 1) : d181588 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d132742, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132742, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132743 q = 1) (hb : d180908 q = 1) : d181589 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d132743, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132743, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132744 q = 1) (hb : d180908 q = 1) : d181590 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d132744, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132744, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132745 q = 1) (hb : d180908 q = 1) : d181591 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d132745, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132745, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42901 (p : Pattern) (ha : d132751 p = 1) (hb : d180908 p = 1) : d181597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132746 q = 1) (hb : d180908 q = 1) : d181592 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d132746, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42900 q ha hb
    | true =>
      simp only [d132746, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132747 q = 1) (hb : d180908 q = 1) : d181593 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d132747, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132747, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132748 q = 1) (hb : d180908 q = 1) : d181594 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d132748, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132748, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132749 q = 1) (hb : d180908 q = 1) : d181595 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d132749, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132749, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132750 q = 1) (hb : d180908 q = 1) : d181596 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d132750, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132750, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132751 q = 1) (hb : d180908 q = 1) : d181597 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d132751, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132751, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42902 (p : Pattern) (ha : d132757 p = 1) (hb : d180908 p = 1) : d181603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132752 q = 1) (hb : d180908 q = 1) : d181598 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d132752, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42901 q ha hb
    | true =>
      simp only [d132752, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132753 q = 1) (hb : d180908 q = 1) : d181599 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d132753, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132753, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132754 q = 1) (hb : d180908 q = 1) : d181600 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d132754, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132754, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132755 q = 1) (hb : d180908 q = 1) : d181601 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d132755, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132755, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132756 q = 1) (hb : d180908 q = 1) : d181602 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d132756, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132756, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132757 q = 1) (hb : d180908 q = 1) : d181603 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d132757, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132757, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42903 (p : Pattern) (ha : d132763 p = 1) (hb : d180908 p = 1) : d181609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132758 q = 1) (hb : d180908 q = 1) : d181604 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d132758, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42902 q ha hb
    | true =>
      simp only [d132758, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132759 q = 1) (hb : d180908 q = 1) : d181605 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d132759, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132759, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132760 q = 1) (hb : d180908 q = 1) : d181606 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d132760, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132760, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132761 q = 1) (hb : d180908 q = 1) : d181607 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d132761, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132761, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132762 q = 1) (hb : d180908 q = 1) : d181608 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d132762, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132762, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132763 q = 1) (hb : d180908 q = 1) : d181609 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d132763, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132763, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42904 (p : Pattern) (ha : d128584 p = 1) (hb : d180912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18534 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128581 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128582 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128583 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128583, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128583, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128584 q = 1) (hb : d180912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128584, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128584, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro42905 (p : Pattern) (ha : d128590 p = 1) (hb : d180918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128585 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128585, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
    | true =>
      simp only [d128585, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128586 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128586, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128586, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128587 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128587, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128587, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128588 q = 1) (hb : d180916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128588, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128588, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128589 q = 1) (hb : d180917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128589, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128589, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128590 q = 1) (hb : d180918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128590, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128590, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42906 (p : Pattern) (ha : d128596 p = 1) (hb : d180924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128591 q = 1) (hb : d180919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128591, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42905 q ha hb
    | true =>
      simp only [d128591, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128592 q = 1) (hb : d180920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128592, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128592, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128593 q = 1) (hb : d180921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128593, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128593, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128594 q = 1) (hb : d180922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128594, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128594, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128595 q = 1) (hb : d180923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128595, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128595, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128596 q = 1) (hb : d180924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128596, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128596, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42907 (p : Pattern) (ha : d128602 p = 1) (hb : d180930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128597 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42906 q ha hb
    | true =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128598 q = 1) (hb : d180926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128598, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128598, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128599 q = 1) (hb : d180927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128599, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128599, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128600 q = 1) (hb : d180928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128600, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128600, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128601 q = 1) (hb : d180929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128601, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128601, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128602 q = 1) (hb : d180930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128602, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128602, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42908 (p : Pattern) (ha : d128608 p = 1) (hb : d180936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128603 q = 1) (hb : d180931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128603, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128603, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42907 q ha hb
  have h2 (q : Pattern) (ha : d128604 q = 1) (hb : d180932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128604, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128604, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128605 q = 1) (hb : d180933 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128605, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128605, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128606 q = 1) (hb : d180934 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128606, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128606, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128607 q = 1) (hb : d180935 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128607, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128607, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128608 q = 1) (hb : d180936 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128608, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128608, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42909 (p : Pattern) (ha : d128616 p = 1) (hb : d180944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18571 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18571, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128613 q = 1) (hb : d180941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128613, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128613, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128614 q = 1) (hb : d180942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128614, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128614, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18534 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128581 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128582 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128615 q = 1) (hb : d180943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128615, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128615, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128583 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128583, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128583, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128616 q = 1) (hb : d180944 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128616, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128616, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42910 (p : Pattern) (ha : d128622 p = 1) (hb : d180950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128617 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
    | true =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
  have h2 (q : Pattern) (ha : d128618 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128619 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128585 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128585, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
    | true =>
      simp only [d128585, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128586 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128586, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128586, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128587 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128587, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128587, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128620 q = 1) (hb : d180948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128620, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128620, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128588 q = 1) (hb : d180916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128588, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128588, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128621 q = 1) (hb : d180949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128621, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128621, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128622 q = 1) (hb : d180950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128622, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128622, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro42911 (p : Pattern) (ha : d128628 p = 1) (hb : d180956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128623 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128623, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42910 q ha hb
    | true =>
      simp only [d128623, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128624 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128624, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128624, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128591 q = 1) (hb : d180919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128591, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42905 q ha hb
    | true =>
      simp only [d128591, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128592 q = 1) (hb : d180920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128592, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128592, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128625 q = 1) (hb : d180953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128625, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128625, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128626 q = 1) (hb : d180954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128626, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128626, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128627 q = 1) (hb : d180955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128627, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128627, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128628 q = 1) (hb : d180956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128628, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128628, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42912 (p : Pattern) (ha : d128634 p = 1) (hb : d180962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128629 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128629, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42911 q ha hb
    | true =>
      simp only [d128629, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42906 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128597 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128630 q = 1) (hb : d180958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128630, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128630, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128597 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42906 q ha hb
    | true =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128598 q = 1) (hb : d180926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128598, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128598, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128631 q = 1) (hb : d180959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128631, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128631, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128632 q = 1) (hb : d180960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128632, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128632, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128633 q = 1) (hb : d180961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128633, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128633, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128634 q = 1) (hb : d180962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128634, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128634, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42913 (p : Pattern) (ha : d128640 p = 1) (hb : d180968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128635 q = 1) (hb : d180963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128635, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128635, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42912 q ha hb
  have h2 (q : Pattern) (ha : d128636 q = 1) (hb : d180964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128636, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128636, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128637 q = 1) (hb : d180965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128637, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128637, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128638 q = 1) (hb : d180966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128638, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128638, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128639 q = 1) (hb : d180967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128639, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128639, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128640 q = 1) (hb : d180968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128640, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128640, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42914 (p : Pattern) (ha : d128652 p = 1) (hb : d180980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18631 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18631, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18631, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128646 q = 1) (hb : d180974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128646, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128646, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128647 q = 1) (hb : d180975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128647, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128647, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18571 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18571, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128613 q = 1) (hb : d180941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128613, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128613, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128614 q = 1) (hb : d180942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128614, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128614, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128648 q = 1) (hb : d180976 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128648, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128648, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d18635 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128649 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128649, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128649, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128650 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128650, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128650, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d18534 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128581 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128582 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128651 q = 1) (hb : d180979 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128651, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128651, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d128652 q = 1) (hb : d180980 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128652, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128652, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42915 (p : Pattern) (ha : d128658 p = 1) (hb : d180986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128653 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128653, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42914 q ha hb
    | true =>
      simp only [d128653, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
  have h2 (q : Pattern) (ha : d128654 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128654, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128654, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128655 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128655, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128655, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128617 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
    | true =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
  have h5 (q : Pattern) (ha : d128618 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128619 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128656 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128656, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128656, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128585 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128585, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
    | true =>
      simp only [d128585, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128586 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128586, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128586, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128587 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128587, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128587, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128620 q = 1) (hb : d180948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128620, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128620, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128657 q = 1) (hb : d180985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128657, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128657, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128658 q = 1) (hb : d180986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128658, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128658, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro42916 (p : Pattern) (ha : d128664 p = 1) (hb : d180992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128659 q = 1) (hb : d180987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128659, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42915 q ha hb
    | true =>
      simp only [d128659, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128660 q = 1) (hb : d180988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128660, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128660, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128623 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128623, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42910 q ha hb
    | true =>
      simp only [d128623, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128624 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128624, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128624, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128661 q = 1) (hb : d180989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128661, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128661, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128662 q = 1) (hb : d180990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128662, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128662, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128663 q = 1) (hb : d180991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128663, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128663, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128664 q = 1) (hb : d180992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128664, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128664, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42917 (p : Pattern) (ha : d128670 p = 1) (hb : d180998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128623 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128623, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42910 q ha hb
    | true =>
      simp only [d128623, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128624 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128624, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128624, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128667 q = 1) (hb : d180995 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128667, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128667, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128668 q = 1) (hb : d180996 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128668, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128668, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128669 q = 1) (hb : d180997 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128669, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128669, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128670 q = 1) (hb : d180998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128670, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128670, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42918 (p : Pattern) (ha : d128676 p = 1) (hb : d181004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128665 q = 1) (hb : d180993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128665, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42916 q ha hb
    | true =>
      simp only [d128665, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42911 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128666 q = 1) (hb : d180994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128666, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128666, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128671 q = 1) (hb : d180999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128671, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42917 q ha hb
    | true =>
      simp only [d128671, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128672 q = 1) (hb : d181000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128672, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128672, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128673 q = 1) (hb : d181001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128673, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128673, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128674 q = 1) (hb : d181002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128674, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128674, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128675 q = 1) (hb : d181003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128675, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128675, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128676 q = 1) (hb : d181004 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128676, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128676, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42919 (p : Pattern) (ha : d128682 p = 1) (hb : d181010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128597 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42906 q ha hb
    | true =>
      simp only [d128597, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128678 q = 1) (hb : d181006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128678, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128678, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128679 q = 1) (hb : d181007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128679, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128679, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128680 q = 1) (hb : d181008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128680, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128680, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128681 q = 1) (hb : d181009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128681, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128681, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128682 q = 1) (hb : d181010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128682, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128682, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42920 (p : Pattern) (ha : d128688 p = 1) (hb : d181016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128677 q = 1) (hb : d181005 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128677, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128677, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42918 q ha hb
  have h2 (q : Pattern) (ha : d128683 q = 1) (hb : d181011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128683, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128683, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42919 q ha hb
  have h3 (q : Pattern) (ha : d128684 q = 1) (hb : d181012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128684, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128684, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128685 q = 1) (hb : d181013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128685, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128685, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128686 q = 1) (hb : d181014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128686, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128686, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128687 q = 1) (hb : d181015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128687, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128687, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128688 q = 1) (hb : d181016 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128688, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128688, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42921 (p : Pattern) (ha : d128694 p = 1) (hb : d181022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128609 q = 1) (hb : d180937 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128609, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128609, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42908 q ha hb
  have h2 (q : Pattern) (ha : d128610 q = 1) (hb : d180938 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128610, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128610, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128611 q = 1) (hb : d180939 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128611, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128611, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128612 q = 1) (hb : d180940 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128612, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128612, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128641 q = 1) (hb : d180969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128641, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128641, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42913 q ha hb
  have h6 (q : Pattern) (ha : d128642 q = 1) (hb : d180970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128642, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128642, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128643 q = 1) (hb : d180971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128643, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128643, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128644 q = 1) (hb : d180972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128644, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128644, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128645 q = 1) (hb : d180973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128645, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128645, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128689 q = 1) (hb : d181017 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128689, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128689, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42920 q ha hb
  have h11 (q : Pattern) (ha : d128690 q = 1) (hb : d181018 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128690, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128690, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128691 q = 1) (hb : d181019 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128691, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128691, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128692 q = 1) (hb : d181020 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128692, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128692, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128693 q = 1) (hb : d181021 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128693, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128693, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128694 q = 1) (hb : d181022 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128694, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128694, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42922 (p : Pattern) (ha : d128703 p = 1) (hb : d181031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18708 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18708, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18708, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128695 q = 1) (hb : d181023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128695, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128695, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128696 q = 1) (hb : d181024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128696, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128696, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18711 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128697 q = 1) (hb : d181025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128697, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128697, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128698 q = 1) (hb : d181026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128698, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128698, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128699 q = 1) (hb : d181027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128699, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128699, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d18715 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128700 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128701 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d18635 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128649 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128649, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d128649, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128650 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128650, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128650, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128702 q = 1) (hb : d181030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128702, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128702, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d128703 q = 1) (hb : d181031 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128703, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128703, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42923 (p : Pattern) (ha : d128707 p = 1) (hb : d181035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18635 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128649 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128649, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128649, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128650 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128650, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128650, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18534 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128581 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128581, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128582 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128582, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128651 q = 1) (hb : d180979 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128651, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128651, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128583 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128583, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128583, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128707 q = 1) (hb : d181035 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128707, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128707, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42924 (p : Pattern) (ha : d128713 p = 1) (hb : d181041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128704 q = 1) (hb : d181032 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128704, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42922 q ha hb
    | true =>
      simp only [d128704, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42914 q ha hb
  have h2 (q : Pattern) (ha : d128705 q = 1) (hb : d181033 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128705, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128705, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128706 q = 1) (hb : d181034 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128706, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128706, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128708 q = 1) (hb : d181036 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128708, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42914 q ha hb
    | true =>
      simp only [d128708, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42923 q ha hb
  have h5 (q : Pattern) (ha : d128709 q = 1) (hb : d181037 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128709, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128709, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128710 q = 1) (hb : d181038 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128710, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128710, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128711 q = 1) (hb : d181039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128711, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128711, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128653 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128653, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42914 q ha hb
    | true =>
      simp only [d128653, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
  have h9 (q : Pattern) (ha : d128654 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128654, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128654, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128655 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128655, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128655, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128617 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
    | true =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
  have h12 (q : Pattern) (ha : d128618 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128619 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128656 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128656, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128656, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128712 q = 1) (hb : d181040 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128712, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128712, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128713 q = 1) (hb : d181041 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128713, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128713, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro42925 (p : Pattern) (ha : d128718 p = 1) (hb : d181046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128653 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128653, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42914 q ha hb
    | true =>
      simp only [d128653, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
  have h2 (q : Pattern) (ha : d128654 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128654, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128654, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128655 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128655, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128655, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128617 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
    | true =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
  have h5 (q : Pattern) (ha : d128618 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128619 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128656 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128656, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128656, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128716 q = 1) (hb : d181044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128716, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128716, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128717 q = 1) (hb : d181045 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128717, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128717, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128718 q = 1) (hb : d181046 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128718, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128718, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro42926 (p : Pattern) (ha : d128724 p = 1) (hb : d181052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128714 q = 1) (hb : d181042 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128714, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42924 q ha hb
    | true =>
      simp only [d128714, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128715 q = 1) (hb : d181043 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128715, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128715, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128719 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128719, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42925 q ha hb
    | true =>
      simp only [d128719, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128720 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128720, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128720, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128721 q = 1) (hb : d181049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128721, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128721, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128722 q = 1) (hb : d181050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128722, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128722, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128723 q = 1) (hb : d181051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128723, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128723, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128724 q = 1) (hb : d181052 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128724, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128724, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42927 (p : Pattern) (ha : d128726 p = 1) (hb : d181054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128617 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42909 q ha hb
    | true =>
      simp only [d128617, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42904 q ha hb
  have h2 (q : Pattern) (ha : d128618 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128618, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128619 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128619, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128716 q = 1) (hb : d181044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128716, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128716, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128725 q = 1) (hb : d181053 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128725, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128725, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128726 q = 1) (hb : d181054 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128726, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128726, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42928 (p : Pattern) (ha : d128732 p = 1) (hb : d181060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128719 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128719, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42925 q ha hb
    | true =>
      simp only [d128719, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128720 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128720, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128720, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128727 q = 1) (hb : d181055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128727, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42927 q ha hb
    | true =>
      simp only [d128727, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128728 q = 1) (hb : d181056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128728, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128728, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128729 q = 1) (hb : d181057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128729, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128729, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128730 q = 1) (hb : d181058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128730, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128730, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128731 q = 1) (hb : d181059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128731, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128731, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128732 q = 1) (hb : d181060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128732, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128732, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42929 (p : Pattern) (ha : d128743 p = 1) (hb : d181066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128719 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128719, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42925 q ha hb
    | true =>
      simp only [d128719, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128720 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128720, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128720, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128740 q = 1) (hb : d181063 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128740, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128740, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128741 q = 1) (hb : d181064 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128741, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128741, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128742 q = 1) (hb : d181065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128742, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128742, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128743 q = 1) (hb : d181066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128743, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128743, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42930 (p : Pattern) (ha : d128749 p = 1) (hb : d181072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128733 q = 1) (hb : d181061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128733, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42926 q ha hb
    | true =>
      simp only [d128733, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42928 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128738 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128739 q = 1) (hb : d181062 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128739, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128739, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128744 q = 1) (hb : d181067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128744, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42929 q ha hb
    | true =>
      simp only [d128744, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128745 q = 1) (hb : d181068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128745, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128745, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128746 q = 1) (hb : d181069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128746, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128746, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128747 q = 1) (hb : d181070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128747, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128747, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128748 q = 1) (hb : d181071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128748, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128748, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128749 q = 1) (hb : d181072 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128749, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128749, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42931 (p : Pattern) (ha : d128737 p = 1) (hb : d181077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128727 q = 1) (hb : d181055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128727, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42927 q ha hb
    | true =>
      simp only [d128727, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128728 q = 1) (hb : d181056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128728, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128728, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128734 q = 1) (hb : d181074 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128734, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128734, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128735 q = 1) (hb : d181075 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128735, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128735, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128736 q = 1) (hb : d181076 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128736, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128736, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128737 q = 1) (hb : d181077 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128737, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128737, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42932 (p : Pattern) (ha : d128756 p = 1) (hb : d181083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128751 q = 1) (hb : d181078 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128751, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42931 q ha hb
    | true =>
      simp only [d128751, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128752 q = 1) (hb : d181079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128752, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128752, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128753 q = 1) (hb : d181080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128753, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128753, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128754 q = 1) (hb : d181081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128754, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128754, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128755 q = 1) (hb : d181082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128755, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128755, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128756 q = 1) (hb : d181083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128756, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128756, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42933 (p : Pattern) (ha : d128762 p = 1) (hb : d181089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128750 q = 1) (hb : d181073 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128750, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128750, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42930 q ha hb
  have h2 (q : Pattern) (ha : d128757 q = 1) (hb : d181084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128757, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128757, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42932 q ha hb
  have h3 (q : Pattern) (ha : d128758 q = 1) (hb : d181085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128758, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128758, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128759 q = 1) (hb : d181086 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128759, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128759, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128760 q = 1) (hb : d181087 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128760, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128760, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128761 q = 1) (hb : d181088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128761, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128761, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128762 q = 1) (hb : d181089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128762, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128762, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42934 (p : Pattern) (ha : d128768 p = 1) (hb : d181095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128763 q = 1) (hb : d181090 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128763, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128763, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42933 q ha hb
  have h2 (q : Pattern) (ha : d128764 q = 1) (hb : d181091 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128764, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128764, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128765 q = 1) (hb : d181092 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128765, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128765, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128766 q = 1) (hb : d181093 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128766, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128766, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128767 q = 1) (hb : d181094 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128767, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128767, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128768 q = 1) (hb : d181095 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128768, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128768, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42935 (p : Pattern) (ha : d128778 p = 1) (hb : d181105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18831 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18831, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18831, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128770 q = 1) (hb : d181097 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128770, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128770, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128771 q = 1) (hb : d181098 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128771, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128771, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16356 q = 1) (hb : d127213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18834 q = 1) (hb : d127214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18834, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18834, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128772 q = 1) (hb : d181099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128772, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128772, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128773 q = 1) (hb : d181100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128773, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128773, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128774 q = 1) (hb : d181101 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128774, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128774, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14644 q = 1) (hb : d122847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d18838 q = 1) (hb : d122848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18838, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18838, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128775 q = 1) (hb : d181102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128775, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128775, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128776 q = 1) (hb : d181103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128776, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128776, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d18715 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128700 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128701 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128777 q = 1) (hb : d181104 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128777, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128777, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d128778 q = 1) (hb : d181105 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128778, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128778, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42936 (p : Pattern) (ha : d128782 p = 1) (hb : d181109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18708 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18708, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18708, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128695 q = 1) (hb : d181023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128695, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128695, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128696 q = 1) (hb : d181024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128696, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128696, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18711 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128697 q = 1) (hb : d181025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128697, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128697, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128698 q = 1) (hb : d181026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128698, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128698, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128699 q = 1) (hb : d181027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128699, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128699, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d18715 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128700 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128701 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d18843 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128779 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128780 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128781 q = 1) (hb : d181108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128781, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128781, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d128782 q = 1) (hb : d181109 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128782, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128782, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42937 (p : Pattern) (ha : d128787 p = 1) (hb : d181114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18715 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128700 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128700, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128701 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128701, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18843 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128779 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128780 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128781 q = 1) (hb : d181108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128781, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128781, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128786 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128786, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128786, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128787 q = 1) (hb : d181114 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128787, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128787, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42938 (p : Pattern) (ha : d128793 p = 1) (hb : d181120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18631 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18631, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18631, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128646 q = 1) (hb : d180974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128646, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128646, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128647 q = 1) (hb : d180975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128647, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128647, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18843 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128779 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128780 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128792 q = 1) (hb : d181119 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128792, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128792, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128786 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128786, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128786, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128793 q = 1) (hb : d181120 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128793, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128793, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42939 (p : Pattern) (ha : d128797 p = 1) (hb : d181124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18843 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128779 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128779, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128780 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128780, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128786 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128786, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128786, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128797 q = 1) (hb : d181124 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128797, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128797, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro42940 (p : Pattern) (ha : d128803 p = 1) (hb : d181130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128783 q = 1) (hb : d181110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128783, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42935 q ha hb
    | true =>
      simp only [d128783, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42936 q ha hb
  have h2 (q : Pattern) (ha : d128784 q = 1) (hb : d181111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128784, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128784, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128785 q = 1) (hb : d181112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128785, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128785, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128788 q = 1) (hb : d181115 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128788, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42936 q ha hb
    | true =>
      simp only [d128788, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42937 q ha hb
  have h5 (q : Pattern) (ha : d128789 q = 1) (hb : d181116 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128789, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128789, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128790 q = 1) (hb : d181117 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128790, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128790, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128791 q = 1) (hb : d181118 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128791, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128791, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128794 q = 1) (hb : d181121 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128794, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42936 q ha hb
    | true =>
      simp only [d128794, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42938 q ha hb
  have h9 (q : Pattern) (ha : d128795 q = 1) (hb : d181122 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128795, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128795, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128796 q = 1) (hb : d181123 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128796, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128796, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128798 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128798, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42938 q ha hb
    | true =>
      simp only [d128798, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42939 q ha hb
  have h12 (q : Pattern) (ha : d128799 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128799, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128799, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128800 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128800, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128800, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128801 q = 1) (hb : d181128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128801, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128801, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128802 q = 1) (hb : d181129 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128802, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128802, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128803 q = 1) (hb : d181130 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128803, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128803, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro42941 (p : Pattern) (ha : d128808 p = 1) (hb : d181135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128794 q = 1) (hb : d181121 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128794, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42936 q ha hb
    | true =>
      simp only [d128794, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42938 q ha hb
  have h2 (q : Pattern) (ha : d128795 q = 1) (hb : d181122 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128795, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128795, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128796 q = 1) (hb : d181123 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128796, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128796, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128798 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128798, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42938 q ha hb
    | true =>
      simp only [d128798, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42939 q ha hb
  have h5 (q : Pattern) (ha : d128799 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128799, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128799, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128800 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128800, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128800, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128801 q = 1) (hb : d181128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128801, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128801, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128806 q = 1) (hb : d181133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128806, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128806, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128807 q = 1) (hb : d181134 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128807, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128807, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128808 q = 1) (hb : d181135 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128808, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128808, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro42942 (p : Pattern) (ha : d128814 p = 1) (hb : d181141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128804 q = 1) (hb : d181131 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128804, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42940 q ha hb
    | true =>
      simp only [d128804, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128805 q = 1) (hb : d181132 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128805, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128805, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128809 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128809, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42941 q ha hb
    | true =>
      simp only [d128809, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128810 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128810, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128810, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128811 q = 1) (hb : d181138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128811, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128811, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128812 q = 1) (hb : d181139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128812, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128812, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128813 q = 1) (hb : d181140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128813, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128813, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128814 q = 1) (hb : d181141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128814, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128814, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42943 (p : Pattern) (ha : d128816 p = 1) (hb : d181143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128798 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128798, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42938 q ha hb
    | true =>
      simp only [d128798, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42939 q ha hb
  have h2 (q : Pattern) (ha : d128799 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128799, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128799, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128800 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128800, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128800, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128806 q = 1) (hb : d181133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128806, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128806, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128815 q = 1) (hb : d181142 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128815, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128815, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128816 q = 1) (hb : d181143 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128816, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128816, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42944 (p : Pattern) (ha : d128822 p = 1) (hb : d181149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128809 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128809, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42941 q ha hb
    | true =>
      simp only [d128809, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128810 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128810, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128810, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128817 q = 1) (hb : d181144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128817, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42943 q ha hb
    | true =>
      simp only [d128817, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128818 q = 1) (hb : d181145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128818, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128818, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128819 q = 1) (hb : d181146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128819, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128819, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128820 q = 1) (hb : d181147 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128820, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128820, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128821 q = 1) (hb : d181148 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128821, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128821, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128822 q = 1) (hb : d181149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128822, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128822, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42945 (p : Pattern) (ha : d128833 p = 1) (hb : d181155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128809 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128809, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42941 q ha hb
    | true =>
      simp only [d128809, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128810 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128810, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128810, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128830 q = 1) (hb : d181152 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128830, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128830, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128831 q = 1) (hb : d181153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128831, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128831, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128832 q = 1) (hb : d181154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128832, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128832, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128833 q = 1) (hb : d181155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128833, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128833, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42946 (p : Pattern) (ha : d128839 p = 1) (hb : d181161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128823 q = 1) (hb : d181150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128823, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42942 q ha hb
    | true =>
      simp only [d128823, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42944 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128828 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128829 q = 1) (hb : d181151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128829, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128829, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128834 q = 1) (hb : d181156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128834, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42945 q ha hb
    | true =>
      simp only [d128834, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128835 q = 1) (hb : d181157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128835, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128835, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128836 q = 1) (hb : d181158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128836, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128836, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128837 q = 1) (hb : d181159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128837, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128837, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128838 q = 1) (hb : d181160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128838, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128838, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128839 q = 1) (hb : d181161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128839, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128839, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42947 (p : Pattern) (ha : d128827 p = 1) (hb : d181166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128817 q = 1) (hb : d181144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128817, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42943 q ha hb
    | true =>
      simp only [d128817, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128818 q = 1) (hb : d181145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128818, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128818, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128824 q = 1) (hb : d181163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128824, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128824, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128825 q = 1) (hb : d181164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128825, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128825, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128826 q = 1) (hb : d181165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128826, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128826, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128827 q = 1) (hb : d181166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128827, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128827, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42948 (p : Pattern) (ha : d128846 p = 1) (hb : d181172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128841 q = 1) (hb : d181167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128841, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42947 q ha hb
    | true =>
      simp only [d128841, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128842 q = 1) (hb : d181168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128842, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128842, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128843 q = 1) (hb : d181169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128843, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128843, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128844 q = 1) (hb : d181170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128844, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128844, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128845 q = 1) (hb : d181171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128845, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128845, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128846 q = 1) (hb : d181172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128846, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128846, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42949 (p : Pattern) (ha : d128852 p = 1) (hb : d181178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128840 q = 1) (hb : d181162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128840, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128840, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42946 q ha hb
  have h2 (q : Pattern) (ha : d128847 q = 1) (hb : d181173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128847, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128847, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42948 q ha hb
  have h3 (q : Pattern) (ha : d128848 q = 1) (hb : d181174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128848, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128848, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128849 q = 1) (hb : d181175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128849, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128849, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128850 q = 1) (hb : d181176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128850, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128850, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128851 q = 1) (hb : d181177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128851, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128851, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128852 q = 1) (hb : d181178 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128852, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128852, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42950 (p : Pattern) (ha : d128858 p = 1) (hb : d181184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128853 q = 1) (hb : d181179 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128853, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128853, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42949 q ha hb
  have h2 (q : Pattern) (ha : d128854 q = 1) (hb : d181180 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128854, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128854, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128855 q = 1) (hb : d181181 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128855, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128855, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128856 q = 1) (hb : d181182 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128856, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128856, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128857 q = 1) (hb : d181183 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128857, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128857, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128858 q = 1) (hb : d181184 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128858, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128858, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42951 (p : Pattern) (ha : d128871 p = 1) (hb : d181197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18991 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18991, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18991, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128861 q = 1) (hb : d181187 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128861, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128861, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128862 q = 1) (hb : d181188 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128862, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128862, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16649 q = 1) (hb : d127450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18994 q = 1) (hb : d127451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18994, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18994, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128863 q = 1) (hb : d181189 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128863, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128863, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128864 q = 1) (hb : d181190 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128864, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128864, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128865 q = 1) (hb : d181191 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128865, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128865, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14987 q = 1) (hb : d123112 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d18998 q = 1) (hb : d123113 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18998, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18998, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128866 q = 1) (hb : d181192 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128866, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128866, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128867 q = 1) (hb : d181193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128867, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128867, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d19001 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128868 q = 1) (hb : d181194 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128868, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d128868, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128869 q = 1) (hb : d181195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128869, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128869, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128870 q = 1) (hb : d181196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128870, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128870, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d128871 q = 1) (hb : d181197 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128871, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128871, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42952 (p : Pattern) (ha : d128880 p = 1) (hb : d181206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19006 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19006, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19006, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128872 q = 1) (hb : d181198 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128872, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128872, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128873 q = 1) (hb : d181199 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128873, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128873, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d16656 q = 1) (hb : d127457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19009 q = 1) (hb : d127458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19009, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19009, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128874 q = 1) (hb : d181200 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128874, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128874, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128875 q = 1) (hb : d181201 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128875, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128875, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128876 q = 1) (hb : d181202 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128876, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128876, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19001 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128868 q = 1) (hb : d181194 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128868, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128868, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128869 q = 1) (hb : d181195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128869, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128869, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d19013 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128877 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128877, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d128877, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128878 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128878, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128878, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128879 q = 1) (hb : d181205 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128879, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128879, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d128880 q = 1) (hb : d181206 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128880, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128880, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42953 (p : Pattern) (ha : d128888 p = 1) (hb : d181214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13160 q = 1) (hb : d113452 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d113452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23317 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101335 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19021 q = 1) (hb : d113453 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19021, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19021, d113453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128884 q = 1) (hb : d181210 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128884, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128884, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128885 q = 1) (hb : d181211 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128885, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128885, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19013 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128877 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128877, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128877, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128878 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128878, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128878, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128886 q = 1) (hb : d181212 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128886, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128886, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128887 q = 1) (hb : d181213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128887, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128887, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128888 q = 1) (hb : d181214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128888, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128888, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42954 (p : Pattern) (ha : d128898 p = 1) (hb : d181224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19031 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19031, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19031, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128893 q = 1) (hb : d181219 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128893, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128893, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128894 q = 1) (hb : d181220 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128894, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128894, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19034 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128895 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128895, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128895, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128896 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128896, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128896, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128897 q = 1) (hb : d181223 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128897, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128897, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19013 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128877 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128877, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128877, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128878 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128878, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128878, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d128887 q = 1) (hb : d181213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128887, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128887, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d128898 q = 1) (hb : d181224 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128898, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128898, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro42955 (p : Pattern) (ha : d128908 p = 1) (hb : d181234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6350 q = 1) (hb : d76090 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d76090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7947 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69108 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19042 q = 1) (hb : d76091 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19042, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19042, d76091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128902 q = 1) (hb : d181228 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128902, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128902, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128903 q = 1) (hb : d181229 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128903, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128903, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128904 q = 1) (hb : d181230 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128904, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128904, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19046 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128905 q = 1) (hb : d181231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128905, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128905, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128906 q = 1) (hb : d181232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128906, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128906, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128907 q = 1) (hb : d181233 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128907, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128907, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128908 q = 1) (hb : d181234 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128908, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128908, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42956 (p : Pattern) (ha : d128914 p = 1) (hb : d181240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128881 q = 1) (hb : d181207 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128881, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42951 q ha hb
    | true =>
      simp only [d128881, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42952 q ha hb
  have h2 (q : Pattern) (ha : d128882 q = 1) (hb : d181208 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128882, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128882, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128883 q = 1) (hb : d181209 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128883, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128883, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128889 q = 1) (hb : d181215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128889, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42952 q ha hb
    | true =>
      simp only [d128889, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42953 q ha hb
  have h5 (q : Pattern) (ha : d128890 q = 1) (hb : d181216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128890, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128890, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128891 q = 1) (hb : d181217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128891, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128891, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128892 q = 1) (hb : d181218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128892, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128892, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128899 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42952 q ha hb
    | true =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
  have h9 (q : Pattern) (ha : d128900 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128901 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128909 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
    | true =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42955 q ha hb
  have h12 (q : Pattern) (ha : d128910 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128911 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128912 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128913 q = 1) (hb : d181239 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128913, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128913, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128914 q = 1) (hb : d181240 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128914, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128914, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro42957 (p : Pattern) (ha : d128919 p = 1) (hb : d181245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128899 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42952 q ha hb
    | true =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
  have h2 (q : Pattern) (ha : d128900 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128901 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128909 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
    | true =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42955 q ha hb
  have h5 (q : Pattern) (ha : d128910 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128911 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128912 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128917 q = 1) (hb : d181243 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128917, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128917, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128918 q = 1) (hb : d181244 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128918, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128918, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128919 q = 1) (hb : d181245 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128919, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128919, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro42958 (p : Pattern) (ha : d128925 p = 1) (hb : d181251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128915 q = 1) (hb : d181241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128915, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42956 q ha hb
    | true =>
      simp only [d128915, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128916 q = 1) (hb : d181242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128916, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128916, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128920 q = 1) (hb : d181246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128920, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42957 q ha hb
    | true =>
      simp only [d128920, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128921 q = 1) (hb : d181247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128921, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128921, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128922 q = 1) (hb : d181248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128922, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128922, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128923 q = 1) (hb : d181249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128923, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128923, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128924 q = 1) (hb : d181250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128924, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128924, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128925 q = 1) (hb : d181251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128925, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128925, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42959 (p : Pattern) (ha : d128927 p = 1) (hb : d181253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19034 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128895 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128895, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128895, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128896 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128896, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128896, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128926 q = 1) (hb : d181252 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128926, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128926, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19046 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128905 q = 1) (hb : d181231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128905, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128905, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d128906 q = 1) (hb : d181232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128906, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128906, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128907 q = 1) (hb : d181233 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128907, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128907, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128927 q = 1) (hb : d181253 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128927, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128927, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42960 (p : Pattern) (ha : d128933 p = 1) (hb : d181259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128928 q = 1) (hb : d181254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128928, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
    | true =>
      simp only [d128928, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42959 q ha hb
  have h2 (q : Pattern) (ha : d128929 q = 1) (hb : d181255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128929, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128929, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128930 q = 1) (hb : d181256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128930, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128930, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128931 q = 1) (hb : d181257 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128931, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128931, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128932 q = 1) (hb : d181258 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128932, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128932, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128933 q = 1) (hb : d181259 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128933, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128933, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42961 (p : Pattern) (ha : d128939 p = 1) (hb : d181265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128920 q = 1) (hb : d181246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128920, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42957 q ha hb
    | true =>
      simp only [d128920, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128921 q = 1) (hb : d181247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128921, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128921, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128934 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128934, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42960 q ha hb
    | true =>
      simp only [d128934, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128935 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128935, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128935, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128936 q = 1) (hb : d181262 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128936, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128936, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128937 q = 1) (hb : d181263 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128937, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128937, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128938 q = 1) (hb : d181264 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128938, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128938, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128939 q = 1) (hb : d181265 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128939, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128939, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42962 (p : Pattern) (ha : d128955 p = 1) (hb : d181268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19034 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128895 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128895, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128895, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128896 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128896, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128896, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128926 q = 1) (hb : d181252 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128926, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128926, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128955 q = 1) (hb : d181268 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128955, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128955, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro42963 (p : Pattern) (ha : d128961 p = 1) (hb : d181274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128899 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42952 q ha hb
    | true =>
      simp only [d128899, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
  have h2 (q : Pattern) (ha : d128900 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128900, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128901 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128901, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128909 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
    | true =>
      simp only [d128909, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42955 q ha hb
  have h5 (q : Pattern) (ha : d128910 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128910, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128911 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128911, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128912 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128912, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128956 q = 1) (hb : d181269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128956, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42954 q ha hb
    | true =>
      simp only [d128956, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42962 q ha hb
  have h9 (q : Pattern) (ha : d128957 q = 1) (hb : d181270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128957, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128957, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128958 q = 1) (hb : d181271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128958, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128958, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128959 q = 1) (hb : d181272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128959, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128959, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d128960 q = 1) (hb : d181273 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128960, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128960, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128961 q = 1) (hb : d181274 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128961, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128961, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro42964 (p : Pattern) (ha : d128967 p = 1) (hb : d181280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128962 q = 1) (hb : d181275 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128962, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42963 q ha hb
    | true =>
      simp only [d128962, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128963 q = 1) (hb : d181276 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128963, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128963, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128964 q = 1) (hb : d181277 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128964, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128964, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128965 q = 1) (hb : d181278 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128965, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128965, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128966 q = 1) (hb : d181279 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128966, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128966, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128967 q = 1) (hb : d181280 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128967, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128967, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42965 (p : Pattern) (ha : d128973 p = 1) (hb : d181286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128940 q = 1) (hb : d181266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128940, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42958 q ha hb
    | true =>
      simp only [d128940, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42961 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128954 q = 1) (hb : d181267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128954, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128954, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128968 q = 1) (hb : d181281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128968, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42964 q ha hb
    | true =>
      simp only [d128968, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128969 q = 1) (hb : d181282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128969, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128969, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128970 q = 1) (hb : d181283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128970, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128970, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128971 q = 1) (hb : d181284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128971, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128971, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128972 q = 1) (hb : d181285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128972, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128972, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128973 q = 1) (hb : d181286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128973, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128973, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42966 (p : Pattern) (ha : d128952 p = 1) (hb : d181291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128934 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128934, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42960 q ha hb
    | true =>
      simp only [d128934, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128935 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128935, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128935, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128949 q = 1) (hb : d181288 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128949, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128949, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128950 q = 1) (hb : d181289 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128950, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128950, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128951 q = 1) (hb : d181290 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128951, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128951, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128952 q = 1) (hb : d181291 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128952, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128952, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42967 (p : Pattern) (ha : d128980 p = 1) (hb : d181297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128975 q = 1) (hb : d181292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128975, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42966 q ha hb
    | true =>
      simp only [d128975, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128976 q = 1) (hb : d181293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128976, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128976, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128977 q = 1) (hb : d181294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128977, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128977, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128978 q = 1) (hb : d181295 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128978, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128978, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128979 q = 1) (hb : d181296 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128979, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128979, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128980 q = 1) (hb : d181297 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128980, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128980, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42968 (p : Pattern) (ha : d128986 p = 1) (hb : d181303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128974 q = 1) (hb : d181287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128974, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128974, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42965 q ha hb
  have h2 (q : Pattern) (ha : d128981 q = 1) (hb : d181298 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128981, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128981, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42967 q ha hb
  have h3 (q : Pattern) (ha : d128982 q = 1) (hb : d181299 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128982, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128982, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128983 q = 1) (hb : d181300 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128983, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128983, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128984 q = 1) (hb : d181301 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128984, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128984, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128985 q = 1) (hb : d181302 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128985, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128985, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128986 q = 1) (hb : d181303 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128986, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128986, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42969 (p : Pattern) (ha : d128992 p = 1) (hb : d181309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128987 q = 1) (hb : d181304 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128987, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128987, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42968 q ha hb
  have h2 (q : Pattern) (ha : d128988 q = 1) (hb : d181305 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128988, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128988, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128989 q = 1) (hb : d181306 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128989, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128989, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128990 q = 1) (hb : d181307 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128990, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128990, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128991 q = 1) (hb : d181308 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128991, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128991, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128992 q = 1) (hb : d181309 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128992, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128992, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42970 (p : Pattern) (ha : d129006 p = 1) (hb : d181323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19223 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19223, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19223, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128996 q = 1) (hb : d181313 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128996, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128996, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128997 q = 1) (hb : d181314 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128997, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128997, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19226 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19226, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19226, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128998 q = 1) (hb : d181315 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128998, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d128998, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128999 q = 1) (hb : d181316 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128999, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128999, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129000 q = 1) (hb : d181317 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129000, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129000, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15380 q = 1) (hb : d123419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19230 q = 1) (hb : d123420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19230, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19230, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129001 q = 1) (hb : d181318 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129001, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d129001, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d129002 q = 1) (hb : d181319 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129002, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129002, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d19233 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d129003 q = 1) (hb : d181320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129003, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d129003, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d129004 q = 1) (hb : d181321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129004, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d129004, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d129005 q = 1) (hb : d181322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129005, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d129005, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d129006 q = 1) (hb : d181323 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129006, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129006, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42971 (p : Pattern) (ha : d129015 p = 1) (hb : d181332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19238 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19238, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19238, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129007 q = 1) (hb : d181324 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129007, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129007, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129008 q = 1) (hb : d181325 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129008, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129008, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17011 q = 1) (hb : d127745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19241 q = 1) (hb : d127746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19241, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19241, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129009 q = 1) (hb : d181326 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129009, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d129009, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d129010 q = 1) (hb : d181327 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129010, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129010, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129011 q = 1) (hb : d181328 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129011, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129011, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19233 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129003 q = 1) (hb : d181320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129003, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d129003, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d129004 q = 1) (hb : d181321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129004, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129004, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d19245 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d129012 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129012, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d129012, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d129013 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129013, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d129013, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d129014 q = 1) (hb : d181331 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129014, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d129014, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d129015 q = 1) (hb : d181332 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129015, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129015, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42972 (p : Pattern) (ha : d129023 p = 1) (hb : d181340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19253 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19253, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19253, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129019 q = 1) (hb : d181336 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129019, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129019, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129020 q = 1) (hb : d181337 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129020, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129020, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19245 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129012 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129012, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d129012, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d129013 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129013, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129013, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129021 q = 1) (hb : d181338 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129021, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129021, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129022 q = 1) (hb : d181339 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129022, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129022, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129023 q = 1) (hb : d181340 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129023, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129023, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42973 (p : Pattern) (ha : d129033 p = 1) (hb : d181350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19263 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19263, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19263, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129028 q = 1) (hb : d181345 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129028, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129028, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129029 q = 1) (hb : d181346 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129029, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129029, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17027 q = 1) (hb : d127761 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19266 q = 1) (hb : d127762 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19266, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19266, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129030 q = 1) (hb : d181347 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129030, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d129030, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d129031 q = 1) (hb : d181348 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129031, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129031, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129032 q = 1) (hb : d181349 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129032, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129032, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19245 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129012 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129012, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d129012, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d129013 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129013, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129013, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d129022 q = 1) (hb : d181339 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129022, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d129022, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d129033 q = 1) (hb : d181350 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129033, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129033, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro42974 (p : Pattern) (ha : d129043 p = 1) (hb : d181360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69221 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19274 q = 1) (hb : d76226 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19274, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19274, d76226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129037 q = 1) (hb : d181354 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129037, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129037, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129038 q = 1) (hb : d181355 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129038, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129038, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129039 q = 1) (hb : d181356 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129039, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129039, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19278 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129040 q = 1) (hb : d181357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129040, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129040, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129041 q = 1) (hb : d181358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129041, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129041, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129042 q = 1) (hb : d181359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129042, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129042, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129043 q = 1) (hb : d181360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129043, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129043, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42975 (p : Pattern) (ha : d129049 p = 1) (hb : d181366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129016 q = 1) (hb : d181333 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129016, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42970 q ha hb
    | true =>
      simp only [d129016, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42971 q ha hb
  have h2 (q : Pattern) (ha : d129017 q = 1) (hb : d181334 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129017, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129017, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129018 q = 1) (hb : d181335 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129018, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129018, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129024 q = 1) (hb : d181341 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129024, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42971 q ha hb
    | true =>
      simp only [d129024, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42972 q ha hb
  have h5 (q : Pattern) (ha : d129025 q = 1) (hb : d181342 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129025, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129025, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129026 q = 1) (hb : d181343 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129026, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129026, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129027 q = 1) (hb : d181344 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129027, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129027, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129034 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42971 q ha hb
    | true =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
  have h9 (q : Pattern) (ha : d129035 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129036 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129044 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
    | true =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42974 q ha hb
  have h12 (q : Pattern) (ha : d129045 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129046 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129047 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129048 q = 1) (hb : d181365 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129048, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129048, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129049 q = 1) (hb : d181366 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129049, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129049, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro42976 (p : Pattern) (ha : d129054 p = 1) (hb : d181371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129034 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42971 q ha hb
    | true =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
  have h2 (q : Pattern) (ha : d129035 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129036 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129044 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
    | true =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42974 q ha hb
  have h5 (q : Pattern) (ha : d129045 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129046 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129047 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129052 q = 1) (hb : d181369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129052, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129052, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129053 q = 1) (hb : d181370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129053, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129053, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129054 q = 1) (hb : d181371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129054, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129054, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro42977 (p : Pattern) (ha : d129060 p = 1) (hb : d181377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129050 q = 1) (hb : d181367 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129050, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42975 q ha hb
    | true =>
      simp only [d129050, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129051 q = 1) (hb : d181368 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129051, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129051, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129055 q = 1) (hb : d181372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129055, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42976 q ha hb
    | true =>
      simp only [d129055, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129056 q = 1) (hb : d181373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129056, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129056, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129057 q = 1) (hb : d181374 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129057, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129057, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129058 q = 1) (hb : d181375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129058, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129058, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129059 q = 1) (hb : d181376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129059, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129059, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129060 q = 1) (hb : d181377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129060, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129060, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42978 (p : Pattern) (ha : d129064 p = 1) (hb : d181381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19313 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19313, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19313, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129061 q = 1) (hb : d181378 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129061, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129061, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129062 q = 1) (hb : d181379 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129062, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129062, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129063 q = 1) (hb : d181380 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129063, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129063, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19278 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129040 q = 1) (hb : d181357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129040, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129040, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129041 q = 1) (hb : d181358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129041, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129041, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129042 q = 1) (hb : d181359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129042, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129042, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129064 q = 1) (hb : d181381 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129064, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129064, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42979 (p : Pattern) (ha : d129070 p = 1) (hb : d181387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129065 q = 1) (hb : d181382 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129065, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
    | true =>
      simp only [d129065, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42978 q ha hb
  have h2 (q : Pattern) (ha : d129066 q = 1) (hb : d181383 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129066, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129066, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129067 q = 1) (hb : d181384 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129067, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129067, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129068 q = 1) (hb : d181385 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129068, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129068, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129069 q = 1) (hb : d181386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129069, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129069, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129070 q = 1) (hb : d181387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129070, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129070, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42980 (p : Pattern) (ha : d129076 p = 1) (hb : d181393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129055 q = 1) (hb : d181372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129055, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42976 q ha hb
    | true =>
      simp only [d129055, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129056 q = 1) (hb : d181373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129056, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129056, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129071 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129071, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42979 q ha hb
    | true =>
      simp only [d129071, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129072 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129072, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129072, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129073 q = 1) (hb : d181390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129073, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129073, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129074 q = 1) (hb : d181391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129074, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129074, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129075 q = 1) (hb : d181392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129075, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129075, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129076 q = 1) (hb : d181393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129076, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129076, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42981 (p : Pattern) (ha : d129092 p = 1) (hb : d181396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19313 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19313, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19313, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129061 q = 1) (hb : d181378 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129061, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129061, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129062 q = 1) (hb : d181379 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129062, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129062, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129063 q = 1) (hb : d181380 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129063, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129063, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129092 q = 1) (hb : d181396 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129092, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129092, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro42982 (p : Pattern) (ha : d129098 p = 1) (hb : d181402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129034 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42971 q ha hb
    | true =>
      simp only [d129034, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
  have h2 (q : Pattern) (ha : d129035 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129035, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129036 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129036, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129044 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
    | true =>
      simp only [d129044, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42974 q ha hb
  have h5 (q : Pattern) (ha : d129045 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129045, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129046 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129046, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129047 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129047, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129093 q = 1) (hb : d181397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129093, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42973 q ha hb
    | true =>
      simp only [d129093, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42981 q ha hb
  have h9 (q : Pattern) (ha : d129094 q = 1) (hb : d181398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129094, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129094, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129095 q = 1) (hb : d181399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129095, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129095, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129096 q = 1) (hb : d181400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129096, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129096, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129097 q = 1) (hb : d181401 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129097, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129097, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129098 q = 1) (hb : d181402 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129098, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d129098, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro42983 (p : Pattern) (ha : d129104 p = 1) (hb : d181408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129099 q = 1) (hb : d181403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129099, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42982 q ha hb
    | true =>
      simp only [d129099, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129100 q = 1) (hb : d181404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129100, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129100, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129101 q = 1) (hb : d181405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129101, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129101, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129102 q = 1) (hb : d181406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129102, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129102, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129103 q = 1) (hb : d181407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129103, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129103, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129104 q = 1) (hb : d181408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129104, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129104, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42984 (p : Pattern) (ha : d129110 p = 1) (hb : d181414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129077 q = 1) (hb : d181394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129077, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42977 q ha hb
    | true =>
      simp only [d129077, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42980 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129090 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129091 q = 1) (hb : d181395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129091, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129091, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129105 q = 1) (hb : d181409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129105, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42983 q ha hb
    | true =>
      simp only [d129105, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129106 q = 1) (hb : d181410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129106, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129106, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129107 q = 1) (hb : d181411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129107, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129107, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129108 q = 1) (hb : d181412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129108, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129108, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129109 q = 1) (hb : d181413 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129109, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129109, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129110 q = 1) (hb : d181414 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129110, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129110, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42985 (p : Pattern) (ha : d129089 p = 1) (hb : d181419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129071 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129071, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42979 q ha hb
    | true =>
      simp only [d129071, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129072 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129072, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129072, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129086 q = 1) (hb : d181416 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129086, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129086, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129087 q = 1) (hb : d181417 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129087, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129087, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129088 q = 1) (hb : d181418 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129088, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129088, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129089 q = 1) (hb : d181419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129089, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129089, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42986 (p : Pattern) (ha : d129117 p = 1) (hb : d181425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129112 q = 1) (hb : d181420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129112, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42985 q ha hb
    | true =>
      simp only [d129112, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129113 q = 1) (hb : d181421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129113, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129113, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129114 q = 1) (hb : d181422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129114, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129114, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129115 q = 1) (hb : d181423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129115, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129115, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129116 q = 1) (hb : d181424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129116, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129116, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129117 q = 1) (hb : d181425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129117, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129117, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42987 (p : Pattern) (ha : d129123 p = 1) (hb : d181431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129111 q = 1) (hb : d181415 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129111, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129111, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42984 q ha hb
  have h2 (q : Pattern) (ha : d129118 q = 1) (hb : d181426 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129118, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129118, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42986 q ha hb
  have h3 (q : Pattern) (ha : d129119 q = 1) (hb : d181427 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129119, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129119, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129120 q = 1) (hb : d181428 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129120, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129120, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129121 q = 1) (hb : d181429 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129121, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129121, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129122 q = 1) (hb : d181430 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129122, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129122, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129123 q = 1) (hb : d181431 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129123, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129123, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42988 (p : Pattern) (ha : d129129 p = 1) (hb : d181437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129124 q = 1) (hb : d181432 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129124, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129124, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42987 q ha hb
  have h2 (q : Pattern) (ha : d129125 q = 1) (hb : d181433 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129125, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129125, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129126 q = 1) (hb : d181434 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129126, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129126, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129127 q = 1) (hb : d181435 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129127, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129127, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129128 q = 1) (hb : d181436 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129128, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129128, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129129 q = 1) (hb : d181437 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129129, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129129, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42989 (p : Pattern) (ha : d129142 p = 1) (hb : d181450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19462 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19462, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19462, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129134 q = 1) (hb : d181442 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129134, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129134, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129135 q = 1) (hb : d181443 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129135, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129135, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19465 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19465, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19465, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129136 q = 1) (hb : d181444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129136, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d129136, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d129137 q = 1) (hb : d181445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129137, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129137, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129138 q = 1) (hb : d181446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129138, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129138, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19469 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129139 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129139, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d129139, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d129140 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129140, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129140, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d129141 q = 1) (hb : d181449 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129141, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129141, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d129142 q = 1) (hb : d181450 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129142, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129142, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro42990 (p : Pattern) (ha : d129151 p = 1) (hb : d181459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19474 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19474, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19474, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129143 q = 1) (hb : d181451 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129143, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129143, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129144 q = 1) (hb : d181452 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129144, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129144, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19477 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19477, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19477, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129145 q = 1) (hb : d181453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129145, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d129145, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d129146 q = 1) (hb : d181454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129146, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129146, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129147 q = 1) (hb : d181455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129147, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129147, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19469 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129139 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129139, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d129139, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d129140 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129140, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129140, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d19481 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d129148 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129148, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d129148, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d129149 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129149, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d129149, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d129150 q = 1) (hb : d181458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129150, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d129150, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d129151 q = 1) (hb : d181459 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129151, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129151, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42991 (p : Pattern) (ha : d129156 p = 1) (hb : d181464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19469 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129139 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129139, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129139, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129140 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129140, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129140, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19481 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129148 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129148, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d129148, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d129149 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129149, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129149, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129150 q = 1) (hb : d181458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129150, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129150, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129155 q = 1) (hb : d181463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129155, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129155, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129156 q = 1) (hb : d181464 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129156, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129156, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42992 (p : Pattern) (ha : d129166 p = 1) (hb : d181474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19495 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19495, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19495, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129161 q = 1) (hb : d181469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129161, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129161, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129162 q = 1) (hb : d181470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129162, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129162, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17391 q = 1) (hb : d128053 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19498 q = 1) (hb : d128054 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19498, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19498, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129163 q = 1) (hb : d181471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129163, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d129163, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d129164 q = 1) (hb : d181472 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129164, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129164, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129165 q = 1) (hb : d181473 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129165, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129165, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19481 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129148 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129148, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d129148, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d129149 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129149, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129149, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d129155 q = 1) (hb : d181463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129155, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d129155, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d129166 q = 1) (hb : d181474 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129166, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129166, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro42993 (p : Pattern) (ha : d129176 p = 1) (hb : d181484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19506 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19506, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19506, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129170 q = 1) (hb : d181478 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129170, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129170, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129171 q = 1) (hb : d181479 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129171, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129171, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129172 q = 1) (hb : d181480 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129172, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129172, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19510 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129173 q = 1) (hb : d181481 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129173, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129173, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129174 q = 1) (hb : d181482 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129174, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129174, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129175 q = 1) (hb : d181483 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129175, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129175, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129176 q = 1) (hb : d181484 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129176, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129176, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42994 (p : Pattern) (ha : d129182 p = 1) (hb : d181490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129152 q = 1) (hb : d181460 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129152, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42989 q ha hb
    | true =>
      simp only [d129152, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42990 q ha hb
  have h2 (q : Pattern) (ha : d129153 q = 1) (hb : d181461 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129153, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129153, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129154 q = 1) (hb : d181462 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129154, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129154, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129157 q = 1) (hb : d181465 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129157, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42990 q ha hb
    | true =>
      simp only [d129157, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42991 q ha hb
  have h5 (q : Pattern) (ha : d129158 q = 1) (hb : d181466 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129158, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129158, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129159 q = 1) (hb : d181467 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129159, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129159, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129160 q = 1) (hb : d181468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129160, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129160, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129167 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42990 q ha hb
    | true =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
  have h9 (q : Pattern) (ha : d129168 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129169 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129177 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
    | true =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42993 q ha hb
  have h12 (q : Pattern) (ha : d129178 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129179 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129180 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129181 q = 1) (hb : d181489 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129181, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129181, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129182 q = 1) (hb : d181490 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129182, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129182, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro42995 (p : Pattern) (ha : d129187 p = 1) (hb : d181495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129167 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42990 q ha hb
    | true =>
      simp only [d129167, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
  have h2 (q : Pattern) (ha : d129168 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129168, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129169 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129169, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129177 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
    | true =>
      simp only [d129177, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42993 q ha hb
  have h5 (q : Pattern) (ha : d129178 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129178, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129179 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129179, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129180 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129180, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129185 q = 1) (hb : d181493 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129185, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129185, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129186 q = 1) (hb : d181494 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129186, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129186, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129187 q = 1) (hb : d181495 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129187, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129187, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro42996 (p : Pattern) (ha : d129193 p = 1) (hb : d181501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129183 q = 1) (hb : d181491 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129183, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42994 q ha hb
    | true =>
      simp only [d129183, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129184 q = 1) (hb : d181492 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129184, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129184, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129188 q = 1) (hb : d181496 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129188, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42995 q ha hb
    | true =>
      simp only [d129188, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129189 q = 1) (hb : d181497 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129189, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129189, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129190 q = 1) (hb : d181498 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129190, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129190, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129191 q = 1) (hb : d181499 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129191, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129191, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129192 q = 1) (hb : d181500 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129192, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129192, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129193 q = 1) (hb : d181501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129193, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129193, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42997 (p : Pattern) (ha : d129197 p = 1) (hb : d181505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19545 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19545, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19545, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129194 q = 1) (hb : d181502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129194, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129194, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129195 q = 1) (hb : d181503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129195, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129195, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129196 q = 1) (hb : d181504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129196, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129196, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19510 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129173 q = 1) (hb : d181481 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d129173, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129173, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d129174 q = 1) (hb : d181482 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d129174, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129174, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129175 q = 1) (hb : d181483 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d129175, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d129175, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129197 q = 1) (hb : d181505 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d129197, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129197, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro42998 (p : Pattern) (ha : d129203 p = 1) (hb : d181511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129198 q = 1) (hb : d181506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d129198, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42992 q ha hb
    | true =>
      simp only [d129198, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42997 q ha hb
  have h2 (q : Pattern) (ha : d129199 q = 1) (hb : d181507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d129199, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129199, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129200 q = 1) (hb : d181508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d129200, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129200, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129201 q = 1) (hb : d181509 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d129201, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129201, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129202 q = 1) (hb : d181510 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129202, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129202, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129203 q = 1) (hb : d181511 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129203, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129203, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42999 (p : Pattern) (ha : d129209 p = 1) (hb : d181517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129188 q = 1) (hb : d181496 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129188, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42995 q ha hb
    | true =>
      simp only [d129188, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129189 q = 1) (hb : d181497 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129189, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129189, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129204 q = 1) (hb : d181512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129204, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42998 q ha hb
    | true =>
      simp only [d129204, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129205 q = 1) (hb : d181513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129205, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129205, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129206 q = 1) (hb : d181514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129206, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129206, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129207 q = 1) (hb : d181515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129207, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129207, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129208 q = 1) (hb : d181516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129208, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129208, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129209 q = 1) (hb : d181517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129209, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129209, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
end NetHack.Soko22Hazard87
