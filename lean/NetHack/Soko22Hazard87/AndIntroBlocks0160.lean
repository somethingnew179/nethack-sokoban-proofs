import NetHack.Soko22Hazard87.AndIntroBlocks0159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro40000 (p : Pattern) (ha : d123842 p = 1) (hb : d125706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d125701 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39999 q ha hb
    | true =>
      simp only [d123837, d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d125702 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d125703 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d125704 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d125705 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d125706 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40001 (p : Pattern) (ha : d123848 p = 1) (hb : d125712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d125707 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40000 q ha hb
    | true =>
      simp only [d123843, d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d125708 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d125709 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d125710 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d125711 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d125712 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40002 (p : Pattern) (ha : d123854 p = 1) (hb : d125718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d125713 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40001 q ha hb
    | true =>
      simp only [d123849, d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d125714 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d125715 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d125716 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d125717 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d125718 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40003 (p : Pattern) (ha : d123860 p = 1) (hb : d125724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d125719 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40002 q ha hb
    | true =>
      simp only [d123855, d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d125720 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d125721 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d125722 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d125723 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d125724 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40004 (p : Pattern) (ha : d123866 p = 1) (hb : d125730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d125725 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40003 q ha hb
    | true =>
      simp only [d123861, d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d125726 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d125727 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d125728 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d125729 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d125730 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40005 (p : Pattern) (ha : d123872 p = 1) (hb : d125736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d125731 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40004 q ha hb
    | true =>
      simp only [d123867, d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d125732 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d125733 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d125734 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d125735 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d125736 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40006 (p : Pattern) (ha : d123878 p = 1) (hb : d125742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d125737 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40005 q ha hb
    | true =>
      simp only [d123873, d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d125738 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d125739 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d125740 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d125741 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d125742 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40007 (p : Pattern) (ha : d53655 p = 1) (hb : d129471 p = 1) : d163447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d129471 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d129471 q = 1) : d14001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39445 q ha hb
    | true =>
      simp only [d204, d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d129471 q = 1) : d14057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d288 q = 1) (hb : d129471 q = 1) : d14058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d289 q = 1) (hb : d129471 q = 1) : d14059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d290 q = 1) (hb : d129471 q = 1) : d14060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53655 q = 1) (hb : d129471 q = 1) : d163447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40008 (p : Pattern) (ha : d53665 p = 1) (hb : d129471 p = 1) : d163457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d129471 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d129471 q = 1) : d14033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39449 q ha hb
    | true =>
      simp only [d244, d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d129471 q = 1) : d163453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53662 q = 1) (hb : d129471 q = 1) : d163454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53663 q = 1) (hb : d129471 q = 1) : d163455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53664 q = 1) (hb : d129471 q = 1) : d163456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53665 q = 1) (hb : d129471 q = 1) : d163457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40009 (p : Pattern) (ha : d53671 p = 1) (hb : d129471 p = 1) : d163463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d129471 q = 1) : d14062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39455 q ha hb
    | true =>
      simp only [d292, d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39456 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d129471 q = 1) : d14063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d129471 q = 1) : d163445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d129471 q = 1) : d163446 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d129471 q = 1) : d163448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40007 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d129471 q = 1) : d163449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d129471 q = 1) : d163450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d129471 q = 1) : d163451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d129471 q = 1) : d163452 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d129471 q = 1) : d163458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40008 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d129471 q = 1) : d163459 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d129471 q = 1) : d163460 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d129471 q = 1) : d163461 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d129471 q = 1) : d163462 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d129471 q = 1) : d163463 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40010 (p : Pattern) (ha : d53677 p = 1) (hb : d129471 p = 1) : d163469 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d129471 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d129471 q = 1) : d163464 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40009 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d129471 q = 1) : d163465 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d129471 q = 1) : d163466 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d129471 q = 1) : d163467 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d129471 q = 1) : d163468 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d129471 q = 1) : d163469 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro40011 (p : Pattern) (ha : d129471 p = 1) (hb : d171078 p = 1) : d163472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16052 q = 1) (hb : d129471 q = 1) : d14235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39489 q ha hb
    | true =>
      simp only [d16052, d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39480 q ha hb
  have h2 (q : Pattern) (ha : d16053 q = 1) (hb : d129471 q = 1) : d14236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16054 q = 1) (hb : d129471 q = 1) : d14237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16054, d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16055 q = 1) (hb : d129471 q = 1) : d14238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16056 q = 1) (hb : d129471 q = 1) : d14239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171078 q = 1) : d163472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171078, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171078, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40012 (p : Pattern) (ha : d129471 p = 1) (hb : d171089 p = 1) : d163483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171084 q = 1) : d163478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171084, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39515 q hb ha
    | true =>
      simp only [d171084, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39484 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171085 q = 1) : d163479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171085, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171085, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171086 q = 1) : d163480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171086, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171086, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171087 q = 1) : d163481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171087, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171087, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171088 q = 1) : d163482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171088, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171088, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171089 q = 1) : d163483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171089, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171089, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40013 (p : Pattern) (ha : d129471 p = 1) (hb : d171095 p = 1) : d163489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16058 q = 1) (hb : d129471 q = 1) : d14241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39488 q ha hb
    | true =>
      simp only [d16058, d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39490 q ha hb
  have h2 (q : Pattern) (ha : d16059 q = 1) (hb : d129471 q = 1) : d14242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16059, d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171076 q = 1) : d163470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171076, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171076, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171077 q = 1) : d163471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171077, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171077, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171079 q = 1) : d163473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171079, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171079, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40011 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171080 q = 1) : d163474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171080, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171080, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171081 q = 1) : d163475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171081, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171081, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171082 q = 1) : d163476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171082, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171082, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129471 q = 1) (hb : d171083 q = 1) : d163477 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171083, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171083, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129471 q = 1) (hb : d171090 q = 1) : d163484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171090, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171090, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40012 q ha hb
  have h11 (q : Pattern) (ha : d129471 q = 1) (hb : d171091 q = 1) : d163485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171091, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171091, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129471 q = 1) (hb : d171092 q = 1) : d163486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171092, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171092, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129471 q = 1) (hb : d171093 q = 1) : d163487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171093, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171093, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171094 q = 1) : d163488 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171094, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171094, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171095 q = 1) : d163489 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171095, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171095, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40014 (p : Pattern) (ha : d129471 p = 1) (hb : d171101 p = 1) : d163495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171096 q = 1) : d163490 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171096, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171096, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40013 q ha hb
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171097 q = 1) : d163491 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171097, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171097, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171098 q = 1) : d163492 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171098, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171098, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171099 q = 1) : d163493 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171099, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171099, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171100 q = 1) : d163494 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171100, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171100, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171101 q = 1) : d163495 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171101, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171101, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40015 (p : Pattern) (ha : d129471 p = 1) (hb : d171105 p = 1) : d163499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16249 q = 1) (hb : d129471 q = 1) : d14502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39534 q ha hb
    | true =>
      simp only [d16249, d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39523 q ha hb
  have h2 (q : Pattern) (ha : d16250 q = 1) (hb : d129471 q = 1) : d14503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16251 q = 1) (hb : d129471 q = 1) : d14504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16251, d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16252 q = 1) (hb : d129471 q = 1) : d14505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16253 q = 1) (hb : d129471 q = 1) : d14506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171105 q = 1) : d163499 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171105, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171105, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40016 (p : Pattern) (ha : d129471 p = 1) (hb : d171116 p = 1) : d163510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171111 q = 1) : d163505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171111, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39561 q hb ha
    | true =>
      simp only [d171111, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39528 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171112 q = 1) : d163506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171112, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171112, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171113 q = 1) : d163507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171113, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171113, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171114 q = 1) : d163508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171114, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171114, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171115 q = 1) : d163509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171115, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171115, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171116 q = 1) : d163510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171116, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171116, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40017 (p : Pattern) (ha : d129471 p = 1) (hb : d171122 p = 1) : d163516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16255 q = 1) (hb : d129471 q = 1) : d14508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39533 q ha hb
    | true =>
      simp only [d16255, d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39535 q ha hb
  have h2 (q : Pattern) (ha : d16256 q = 1) (hb : d129471 q = 1) : d14509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16256, d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171103 q = 1) : d163497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171103, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171103, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171104 q = 1) : d163498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171104, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171104, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171106 q = 1) : d163500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171106, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171106, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40015 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171107 q = 1) : d163501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171107, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171107, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171108 q = 1) : d163502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171108, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171108, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171109 q = 1) : d163503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171109, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171109, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129471 q = 1) (hb : d171110 q = 1) : d163504 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171110, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171110, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129471 q = 1) (hb : d171117 q = 1) : d163511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171117, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171117, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40016 q ha hb
  have h11 (q : Pattern) (ha : d129471 q = 1) (hb : d171118 q = 1) : d163512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171118, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171118, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129471 q = 1) (hb : d171119 q = 1) : d163513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171119, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171119, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129471 q = 1) (hb : d171120 q = 1) : d163514 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171120, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171120, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171121 q = 1) : d163515 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171121, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171121, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171122 q = 1) : d163516 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171122, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171122, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40018 (p : Pattern) (ha : d129471 p = 1) (hb : d171128 p = 1) : d163522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171123 q = 1) : d163517 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171123, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171123, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40017 q ha hb
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171124 q = 1) : d163518 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171124, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171124, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171125 q = 1) : d163519 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171125, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171125, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171126 q = 1) : d163520 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171126, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171126, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171127 q = 1) : d163521 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171127, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171127, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171128 q = 1) : d163522 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171128, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171128, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40019 (p : Pattern) (ha : d129471 p = 1) (hb : d171133 p = 1) : d163527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16481 q = 1) (hb : d129471 q = 1) : d14809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39573 q ha hb
    | true =>
      simp only [d16481, d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39574 q ha hb
  have h2 (q : Pattern) (ha : d16482 q = 1) (hb : d129471 q = 1) : d14810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16482, d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16483 q = 1) (hb : d129471 q = 1) : d14811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16483, d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16484 q = 1) (hb : d129471 q = 1) : d14812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16484, d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16485 q = 1) (hb : d129471 q = 1) : d14813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16485, d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171133 q = 1) : d163527 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171133, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171133, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40020 (p : Pattern) (ha : d129471 p = 1) (hb : d171140 p = 1) : d163534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d129471 q = 1) : d15016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39606 q ha hb
    | true =>
      simp only [d16673, d15016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d129471 q = 1) : d15017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d15017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d129471 q = 1) : d15018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d15018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15024 q = 1) (hb : d129471 q = 1) : d15024 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d16676 q = 1) (hb : d129471 q = 1) : d15025 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
    | true =>
      simp only [d16676, d15025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16677 q = 1) (hb : d129471 q = 1) : d15026 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d15026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16678 q = 1) (hb : d129471 q = 1) : d15027 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d15027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16679 q = 1) (hb : d129471 q = 1) : d15028 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15042 q = 1) (hb : d129471 q = 1) : d15042 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16693 q = 1) (hb : d129471 q = 1) : d15043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39581 q ha hb
    | true =>
      simp only [d16693, d15043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16694 q = 1) (hb : d129471 q = 1) : d15044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d15044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16695 q = 1) (hb : d129471 q = 1) : d15045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d15045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16696 q = 1) (hb : d129471 q = 1) : d15046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16696, d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171139 q = 1) : d163533 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171139, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171140 q = 1) : d163534 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171140, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d171140, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro40021 (p : Pattern) (ha : d129471 p = 1) (hb : d171146 p = 1) : d163540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171141 q = 1) : d163535 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171141, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40020 q ha hb
    | true =>
      simp only [d171141, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171142 q = 1) : d163536 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171142, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171142, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16699 q = 1) (hb : d129471 q = 1) : d15049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39582 q ha hb
    | true =>
      simp only [d16699, d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16700 q = 1) (hb : d129471 q = 1) : d15050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16700, d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171143 q = 1) : d163537 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171143, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171143, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171144 q = 1) : d163538 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171144, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171144, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171145 q = 1) : d163539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171145, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171145, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171146 q = 1) : d163540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171146, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171146, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40022 (p : Pattern) (ha : d129471 p = 1) (hb : d171152 p = 1) : d163546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171147 q = 1) : d163541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171147, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40021 q ha hb
    | true =>
      simp only [d171147, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39583 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171148 q = 1) : d163542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171148, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171148, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171149 q = 1) : d163543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171149, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171149, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171150 q = 1) : d163544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171150, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171150, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171151 q = 1) : d163545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171151, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171151, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171152 q = 1) : d163546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171152, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171152, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40023 (p : Pattern) (ha : d129471 p = 1) (hb : d171158 p = 1) : d163552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16487 q = 1) (hb : d129471 q = 1) : d14815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39572 q ha hb
    | true =>
      simp only [d16487, d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39575 q ha hb
  have h2 (q : Pattern) (ha : d16488 q = 1) (hb : d129471 q = 1) : d14816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16488, d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171131 q = 1) : d163525 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171131, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171131, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171132 q = 1) : d163526 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171132, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171132, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171134 q = 1) : d163528 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171134, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171134, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40019 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171135 q = 1) : d163529 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171135, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171135, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171136 q = 1) : d163530 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171136, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171136, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171137 q = 1) : d163531 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171137, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171137, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129471 q = 1) (hb : d171138 q = 1) : d163532 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171138, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171138, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129471 q = 1) (hb : d171153 q = 1) : d163547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171153, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171153, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40022 q ha hb
  have h11 (q : Pattern) (ha : d129471 q = 1) (hb : d171154 q = 1) : d163548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171154, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171154, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129471 q = 1) (hb : d171155 q = 1) : d163549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171155, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171155, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129471 q = 1) (hb : d171156 q = 1) : d163550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171156, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171156, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171157 q = 1) : d163551 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171157, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171157, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171158 q = 1) : d163552 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171158, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171158, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40024 (p : Pattern) (ha : d129471 p = 1) (hb : d171164 p = 1) : d163558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171159 q = 1) : d163553 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171159, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171159, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40023 q ha hb
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171160 q = 1) : d163554 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171160, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171160, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171161 q = 1) : d163555 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171161, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171161, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171162 q = 1) : d163556 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171162, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171162, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171163 q = 1) : d163557 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171163, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171163, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171164 q = 1) : d163558 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171164, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171164, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40025 (p : Pattern) (ha : d129471 p = 1) (hb : d171170 p = 1) : d163564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16833 q = 1) (hb : d129471 q = 1) : d15202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39624 q ha hb
    | true =>
      simp only [d16833, d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39625 q ha hb
  have h2 (q : Pattern) (ha : d16834 q = 1) (hb : d129471 q = 1) : d15203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16834, d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16835 q = 1) (hb : d129471 q = 1) : d15204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16835, d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16836 q = 1) (hb : d129471 q = 1) : d15205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16836, d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16837 q = 1) (hb : d129471 q = 1) : d15206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16837, d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171170 q = 1) : d163564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171170, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171170, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40026 (p : Pattern) (ha : d129471 p = 1) (hb : d171177 p = 1) : d163571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d129471 q = 1) : d15409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39657 q ha hb
    | true =>
      simp only [d17033, d15409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d129471 q = 1) : d15410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d15410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d129471 q = 1) : d15411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d15411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15417 q = 1) (hb : d129471 q = 1) : d15417 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17036 q = 1) (hb : d129471 q = 1) : d15418 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
    | true =>
      simp only [d17036, d15418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17037 q = 1) (hb : d129471 q = 1) : d15419 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d15419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17038 q = 1) (hb : d129471 q = 1) : d15420 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d15420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17039 q = 1) (hb : d129471 q = 1) : d15421 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15435 q = 1) (hb : d129471 q = 1) : d15435 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17053 q = 1) (hb : d129471 q = 1) : d15436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39632 q ha hb
    | true =>
      simp only [d17053, d15436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17054 q = 1) (hb : d129471 q = 1) : d15437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d15437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17055 q = 1) (hb : d129471 q = 1) : d15438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d15438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17056 q = 1) (hb : d129471 q = 1) : d15439 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17056, d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171176 q = 1) : d163570 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171176, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171177 q = 1) : d163571 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171177, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d171177, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro40027 (p : Pattern) (ha : d129471 p = 1) (hb : d171183 p = 1) : d163577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171178 q = 1) : d163572 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171178, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40026 q ha hb
    | true =>
      simp only [d171178, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171179 q = 1) : d163573 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171179, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171179, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17059 q = 1) (hb : d129471 q = 1) : d15442 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39633 q ha hb
    | true =>
      simp only [d17059, d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17060 q = 1) (hb : d129471 q = 1) : d15443 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17060, d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171180 q = 1) : d163574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171180, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171180, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171181 q = 1) : d163575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171181, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171181, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171182 q = 1) : d163576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171182, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171182, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171183 q = 1) : d163577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171183, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171183, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40028 (p : Pattern) (ha : d129471 p = 1) (hb : d171189 p = 1) : d163583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171184 q = 1) : d163578 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171184, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40027 q ha hb
    | true =>
      simp only [d171184, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39634 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171185 q = 1) : d163579 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171185, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171185, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171186 q = 1) : d163580 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171186, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171186, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171187 q = 1) : d163581 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171187, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171187, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171188 q = 1) : d163582 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171188, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171188, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171189 q = 1) : d163583 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171189, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171189, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40029 (p : Pattern) (ha : d129471 p = 1) (hb : d171195 p = 1) : d163589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16839 q = 1) (hb : d129471 q = 1) : d15208 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39623 q ha hb
    | true =>
      simp only [d16839, d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39626 q ha hb
  have h2 (q : Pattern) (ha : d16840 q = 1) (hb : d129471 q = 1) : d15209 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16840, d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171168 q = 1) : d163562 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171168, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171168, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171169 q = 1) : d163563 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171169, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171169, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171171 q = 1) : d163565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171171, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171171, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40025 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171172 q = 1) : d163566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171172, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171172, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171173 q = 1) : d163567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171173, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171173, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171174 q = 1) : d163568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171174, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171174, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129471 q = 1) (hb : d171175 q = 1) : d163569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171175, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171175, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129471 q = 1) (hb : d171190 q = 1) : d163584 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171190, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171190, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40028 q ha hb
  have h11 (q : Pattern) (ha : d129471 q = 1) (hb : d171191 q = 1) : d163585 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171191, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171191, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129471 q = 1) (hb : d171192 q = 1) : d163586 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171192, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171192, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129471 q = 1) (hb : d171193 q = 1) : d163587 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171193, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171193, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171194 q = 1) : d163588 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171194, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171194, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171195 q = 1) : d163589 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171195, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171195, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40030 (p : Pattern) (ha : d129471 p = 1) (hb : d171201 p = 1) : d163595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171196 q = 1) : d163590 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171196, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171196, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40029 q ha hb
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171197 q = 1) : d163591 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171197, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171197, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171198 q = 1) : d163592 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171198, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171198, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171199 q = 1) : d163593 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171199, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171199, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171200 q = 1) : d163594 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171200, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171200, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171201 q = 1) : d163595 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171201, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171201, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40031 (p : Pattern) (ha : d129471 p = 1) (hb : d171208 p = 1) : d163602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17199 q = 1) (hb : d129471 q = 1) : d15594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39675 q ha hb
    | true =>
      simp only [d17199, d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39676 q ha hb
  have h2 (q : Pattern) (ha : d17200 q = 1) (hb : d129471 q = 1) : d15595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17200, d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17201 q = 1) (hb : d129471 q = 1) : d15596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17201, d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17202 q = 1) (hb : d129471 q = 1) : d15597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17202, d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17203 q = 1) (hb : d129471 q = 1) : d15598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17203, d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171208 q = 1) : d163602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171208, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171208, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro40032 (p : Pattern) (ha : d129471 p = 1) (hb : d171215 p = 1) : d163609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d129471 q = 1) : d15787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39708 q ha hb
    | true =>
      simp only [d17397, d15787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d129471 q = 1) : d15788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d15788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d129471 q = 1) : d15789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d15789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15795 q = 1) (hb : d129471 q = 1) : d15795 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d17400 q = 1) (hb : d129471 q = 1) : d15796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
    | true =>
      simp only [d17400, d15796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17401 q = 1) (hb : d129471 q = 1) : d15797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d15797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17402 q = 1) (hb : d129471 q = 1) : d15798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d15798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17403 q = 1) (hb : d129471 q = 1) : d15799 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15813 q = 1) (hb : d129471 q = 1) : d15813 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17417 q = 1) (hb : d129471 q = 1) : d15814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39683 q ha hb
    | true =>
      simp only [d17417, d15814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17418 q = 1) (hb : d129471 q = 1) : d15815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d15815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17419 q = 1) (hb : d129471 q = 1) : d15816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d15816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17420 q = 1) (hb : d129471 q = 1) : d15817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17420, d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171214 q = 1) : d163608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d171214, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171215 q = 1) : d163609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171215, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d171215, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro40033 (p : Pattern) (ha : d129471 p = 1) (hb : d171221 p = 1) : d163615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171216 q = 1) : d163610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171216, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40032 q ha hb
    | true =>
      simp only [d171216, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171217 q = 1) : d163611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171217, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171217, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17423 q = 1) (hb : d129471 q = 1) : d15820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39684 q ha hb
    | true =>
      simp only [d17423, d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17424 q = 1) (hb : d129471 q = 1) : d15821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17424, d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171218 q = 1) : d163612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171218, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171218, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171219 q = 1) : d163613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171219, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171219, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171220 q = 1) : d163614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171220, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171220, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171221 q = 1) : d163615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171221, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171221, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40034 (p : Pattern) (ha : d129471 p = 1) (hb : d171227 p = 1) : d163621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171222 q = 1) : d163616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171222, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40033 q ha hb
    | true =>
      simp only [d171222, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39685 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171223 q = 1) : d163617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171223, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171223, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171224 q = 1) : d163618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171224, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171224, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171225 q = 1) : d163619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171225, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171225, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171226 q = 1) : d163620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171226, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171226, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171227 q = 1) : d163621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171227, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171227, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40035 (p : Pattern) (ha : d129471 p = 1) (hb : d171233 p = 1) : d163627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17205 q = 1) (hb : d129471 q = 1) : d15600 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39674 q ha hb
    | true =>
      simp only [d17205, d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39677 q ha hb
  have h2 (q : Pattern) (ha : d17206 q = 1) (hb : d129471 q = 1) : d15601 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17206, d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171206 q = 1) : d163600 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171206, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d171206, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171207 q = 1) : d163601 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171207, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171207, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171209 q = 1) : d163603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171209, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171209, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40031 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171210 q = 1) : d163604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171210, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171210, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171211 q = 1) : d163605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171211, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171211, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171212 q = 1) : d163606 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171212, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d171212, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129471 q = 1) (hb : d171213 q = 1) : d163607 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171213, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171213, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129471 q = 1) (hb : d171228 q = 1) : d163622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171228, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171228, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40034 q ha hb
  have h11 (q : Pattern) (ha : d129471 q = 1) (hb : d171229 q = 1) : d163623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171229, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171229, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129471 q = 1) (hb : d171230 q = 1) : d163624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171230, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d171230, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129471 q = 1) (hb : d171231 q = 1) : d163625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171231, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d171231, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171232 q = 1) : d163626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171232, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d171232, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171233 q = 1) : d163627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171233, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d171233, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40036 (p : Pattern) (ha : d129471 p = 1) (hb : d171239 p = 1) : d163633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171234 q = 1) : d163628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171234, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171234, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40035 q ha hb
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171235 q = 1) : d163629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171235, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171235, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171236 q = 1) : d163630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171236, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171236, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171237 q = 1) : d163631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171237, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171237, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171238 q = 1) : d163632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171238, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171238, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171239 q = 1) : d163633 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171239, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d171239, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40037 (p : Pattern) (ha : d129471 p = 1) (hb : d171245 p = 1) : d163639 p = 1 := by
  have h0 (q : Pattern) (ha : d129471 q = 1) (hb : d171102 q = 1) : d163496 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171102, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40010 q hb ha
    | true =>
      simp only [d171102, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40014 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171129 q = 1) : d163523 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171129, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171129, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40018 q ha hb
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171130 q = 1) : d163524 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171130, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d171130, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171165 q = 1) : d163559 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171165, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171165, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40024 q ha hb
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171166 q = 1) : d163560 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171166, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171166, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171167 q = 1) : d163561 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171167, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171167, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129471 q = 1) (hb : d171202 q = 1) : d163596 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171202, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171202, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40030 q ha hb
  have h8 (q : Pattern) (ha : d129471 q = 1) (hb : d171203 q = 1) : d163597 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171203, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171203, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129471 q = 1) (hb : d171204 q = 1) : d163598 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171204, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171204, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129471 q = 1) (hb : d171205 q = 1) : d163599 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171205, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d171205, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129471 q = 1) (hb : d171240 q = 1) : d163634 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171240, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171240, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40036 q ha hb
  have h12 (q : Pattern) (ha : d129471 q = 1) (hb : d171241 q = 1) : d163635 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171241, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171241, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129471 q = 1) (hb : d171242 q = 1) : d163636 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171242, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171242, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129471 q = 1) (hb : d171243 q = 1) : d163637 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171243, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d171243, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129471 q = 1) (hb : d171244 q = 1) : d163638 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d171244, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d171244, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129471 q = 1) (hb : d171245 q = 1) : d163639 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d171245, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d171245, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro40038 (p : Pattern) (ha : d129471 p = 1) (hb : d171251 p = 1) : d163645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171246 q = 1) : d163640 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d171246, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40037 q ha hb
    | true =>
      simp only [d171246, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171247 q = 1) : d163641 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d171247, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171247, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171248 q = 1) : d163642 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d171248, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171248, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171249 q = 1) : d163643 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d171249, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171249, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171250 q = 1) : d163644 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d171250, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171250, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171251 q = 1) : d163645 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d171251, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171251, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40039 (p : Pattern) (ha : d129471 p = 1) (hb : d171257 p = 1) : d163651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171252 q = 1) : d163646 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d171252, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40038 q ha hb
    | true =>
      simp only [d171252, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171253 q = 1) : d163647 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d171253, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171253, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171254 q = 1) : d163648 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d171254, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171254, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171255 q = 1) : d163649 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d171255, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171255, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171256 q = 1) : d163650 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d171256, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171256, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171257 q = 1) : d163651 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d171257, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171257, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40040 (p : Pattern) (ha : d129471 p = 1) (hb : d171263 p = 1) : d163657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171258 q = 1) : d163652 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d171258, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40039 q ha hb
    | true =>
      simp only [d171258, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171259 q = 1) : d163653 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d171259, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171259, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171260 q = 1) : d163654 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d171260, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171260, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171261 q = 1) : d163655 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d171261, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171261, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171262 q = 1) : d163656 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d171262, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171262, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171263 q = 1) : d163657 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d171263, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171263, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40041 (p : Pattern) (ha : d129471 p = 1) (hb : d171269 p = 1) : d163663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171264 q = 1) : d163658 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d171264, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40040 q ha hb
    | true =>
      simp only [d171264, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171265 q = 1) : d163659 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d171265, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171265, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171266 q = 1) : d163660 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d171266, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171266, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171267 q = 1) : d163661 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d171267, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171267, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171268 q = 1) : d163662 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d171268, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171268, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171269 q = 1) : d163663 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d171269, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171269, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40042 (p : Pattern) (ha : d129471 p = 1) (hb : d171275 p = 1) : d163669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171270 q = 1) : d163664 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d171270, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40041 q ha hb
    | true =>
      simp only [d171270, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171271 q = 1) : d163665 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d171271, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171271, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171272 q = 1) : d163666 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d171272, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171272, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171273 q = 1) : d163667 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d171273, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171273, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171274 q = 1) : d163668 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d171274, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171274, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171275 q = 1) : d163669 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d171275, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171275, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40043 (p : Pattern) (ha : d129471 p = 1) (hb : d171281 p = 1) : d163675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171276 q = 1) : d163670 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d171276, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40042 q ha hb
    | true =>
      simp only [d171276, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171277 q = 1) : d163671 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d171277, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171277, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171278 q = 1) : d163672 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d171278, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171278, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171279 q = 1) : d163673 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d171279, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171279, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171280 q = 1) : d163674 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d171280, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171280, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171281 q = 1) : d163675 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d171281, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171281, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40044 (p : Pattern) (ha : d129471 p = 1) (hb : d171287 p = 1) : d163681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129471 q = 1) (hb : d171282 q = 1) : d163676 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d171282, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40043 q ha hb
    | true =>
      simp only [d171282, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129471 q = 1) (hb : d171283 q = 1) : d163677 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d171283, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d171283, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129471 q = 1) (hb : d171284 q = 1) : d163678 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d171284, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d171284, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129471 q = 1) (hb : d171285 q = 1) : d163679 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d171285, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d171285, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129471 q = 1) (hb : d171286 q = 1) : d163680 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d171286, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d171286, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129471 q = 1) (hb : d171287 q = 1) : d163681 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d171287, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d171287, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40045 (p : Pattern) (ha : d14054 p = 1) (hb : d122430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13994 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d14050 q = 1) (hb : d122420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14050, d122420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14051 q = 1) (hb : d122427 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14051, d122427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14052 q = 1) (hb : d122428 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14052, d122428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14053 q = 1) (hb : d122429 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14053, d122429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14054 q = 1) (hb : d122430 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d122430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d122430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40046 (p : Pattern) (ha : d14061 p = 1) (hb : d122449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122419 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13994 q = 1) (hb : d122321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39729 q ha hb
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d14050 q = 1) (hb : d122420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14050, d122420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122426 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14051 q = 1) (hb : d122427 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14051, d122427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14052 q = 1) (hb : d122428 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14052, d122428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14053 q = 1) (hb : d122429 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d122429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122435 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122439 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14001 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39731 q ha hb
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d14057 q = 1) (hb : d122442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d122442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14057, d122442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14058 q = 1) (hb : d122446 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d122446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14058, d122446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14059 q = 1) (hb : d122447 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d122447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14059, d122447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14060 q = 1) (hb : d122448 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d122448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14060, d122448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14061 q = 1) (hb : d122449 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d122449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14061, d122449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40047 (p : Pattern) (ha : d122458 p = 1) (hb : d163447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122441 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14001 q = 1) (hb : d122328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39731 q ha hb
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d14057 q = 1) (hb : d122442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d122442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14057, d122442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14058 q = 1) (hb : d122446 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d122446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14058, d122446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14059 q = 1) (hb : d122456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d122456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d122456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14060 q = 1) (hb : d122457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d122457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d122457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122458 q = 1) (hb : d163447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122458, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122458, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40048 (p : Pattern) (ha : d122490 p = 1) (hb : d163457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14033 q = 1) (hb : d122360 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d122360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39736 q ha hb
    | true =>
      simp only [d14033, d122360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d122480 q = 1) (hb : d163453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122480, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122480, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122486 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122487 q = 1) (hb : d163454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122487, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122487, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122488 q = 1) (hb : d163455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122488, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122488, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122489 q = 1) (hb : d163456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122489, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122489, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122490 q = 1) (hb : d163457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122490, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122490, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40049 (p : Pattern) (ha : d122496 p = 1) (hb : d163463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d122450 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d122450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40045 q ha hb
    | true =>
      simp only [d14062, d122450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40046 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14063 q = 1) (hb : d122453 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d122453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, d122453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122454 q = 1) (hb : d163445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122454, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122454, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122455 q = 1) (hb : d163446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122455, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122455, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122459 q = 1) (hb : d163448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122459, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122459, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40047 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122460 q = 1) (hb : d163449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122460, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122460, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122461 q = 1) (hb : d163450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122461, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122461, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122462 q = 1) (hb : d163451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122462, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122462, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122463 q = 1) (hb : d163452 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122463, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122463, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122491 q = 1) (hb : d163458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122491, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122491, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40048 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122492 q = 1) (hb : d163459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122492, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122492, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122493 q = 1) (hb : d163460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122493, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122493, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122494 q = 1) (hb : d163461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122494, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122494, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122495 q = 1) (hb : d163462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122495, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122495, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122496 q = 1) (hb : d163463 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122496, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122496, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40050 (p : Pattern) (ha : d122502 p = 1) (hb : d163469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d122372 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d122372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22453 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d122373 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d122373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d122374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d122374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d122375 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d122375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d122376 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d122376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122497 q = 1) (hb : d163464 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122497, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122497, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40049 q ha hb
  have h8 (q : Pattern) (ha : d122498 q = 1) (hb : d163465 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122498, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122498, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122499 q = 1) (hb : d163466 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122499, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122499, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122500 q = 1) (hb : d163467 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122500, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122500, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122501 q = 1) (hb : d163468 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122501, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122501, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122502 q = 1) (hb : d163469 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122502, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d122502, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro40051 (p : Pattern) (ha : d14230 p = 1) (hb : d122586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14225 q = 1) (hb : d122520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39764 q ha hb
    | true =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39765 q ha hb
  have h5 (q : Pattern) (ha : d14226 q = 1) (hb : d122576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d122576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14226, d122576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14227 q = 1) (hb : d122583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d122583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14227, d122583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14228 q = 1) (hb : d122584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d122584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14228, d122584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14229 q = 1) (hb : d122585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d122585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14229, d122585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14230 q = 1) (hb : d122586 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, d122586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, d122586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40052 (p : Pattern) (ha : d14240 p = 1) (hb : d122607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14225 q = 1) (hb : d122520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39764 q ha hb
    | true =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39765 q ha hb
  have h4 (q : Pattern) (ha : d14226 q = 1) (hb : d122576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d122576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14226, d122576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122582 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14227 q = 1) (hb : d122583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d122583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14227, d122583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14228 q = 1) (hb : d122584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d122584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14228, d122584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14229 q = 1) (hb : d122585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d122585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d122585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122592 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122597 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14235 q = 1) (hb : d122530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d122530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39767 q ha hb
    | true =>
      simp only [d14235, d122530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39768 q ha hb
  have h13 (q : Pattern) (ha : d14236 q = 1) (hb : d122600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d122600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14236, d122600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14237 q = 1) (hb : d122604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d122604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14237, d122604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14238 q = 1) (hb : d122605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d122605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14238, d122605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14239 q = 1) (hb : d122606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d122606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14239, d122606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14240 q = 1) (hb : d122607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, d122607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14240, d122607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40053 (p : Pattern) (ha : d122627 p = 1) (hb : d163472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14235 q = 1) (hb : d122530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d122530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39767 q ha hb
    | true =>
      simp only [d14235, d122530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39768 q ha hb
  have h3 (q : Pattern) (ha : d14236 q = 1) (hb : d122600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d122600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14236, d122600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14237 q = 1) (hb : d122604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d122604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14237, d122604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14238 q = 1) (hb : d122625 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d122625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d122625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14239 q = 1) (hb : d122626 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d122626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d122626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122627 q = 1) (hb : d163472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122627, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122627, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40054 (p : Pattern) (ha : d122683 p = 1) (hb : d163483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122667 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122672 q = 1) (hb : d163478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122672, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39799 q hb ha
    | true =>
      simp only [d122672, d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39774 q hb ha
  have h3 (q : Pattern) (ha : d122673 q = 1) (hb : d163479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122673, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122673, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122679 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122680 q = 1) (hb : d163480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122680, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122680, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122681 q = 1) (hb : d163481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122681, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122681, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122682 q = 1) (hb : d163482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122682, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122682, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122683 q = 1) (hb : d163483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122683, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122683, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40055 (p : Pattern) (ha : d122696 p = 1) (hb : d163489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122538 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d122608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d122608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40051 q ha hb
    | true =>
      simp only [d14241, d122608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40052 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122621 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14242 q = 1) (hb : d122622 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d122622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, d122622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122623 q = 1) (hb : d163470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122623, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122623, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122624 q = 1) (hb : d163471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122624, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122624, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122628 q = 1) (hb : d163473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122628, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122628, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40053 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122630 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122631 q = 1) (hb : d163474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122631, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122631, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122632 q = 1) (hb : d163475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122632, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122632, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122633 q = 1) (hb : d163476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122633, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122633, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122634 q = 1) (hb : d163477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122634, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122634, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122684 q = 1) (hb : d163484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122684, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122684, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40054 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122691 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122692 q = 1) (hb : d163485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122692, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122692, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122693 q = 1) (hb : d163486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122693, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122693, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122694 q = 1) (hb : d163487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122694, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122694, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122695 q = 1) (hb : d163488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122695, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122695, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122696 q = 1) (hb : d163489 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122696, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122696, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40056 (p : Pattern) (ha : d122702 p = 1) (hb : d163495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122697 q = 1) (hb : d163490 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122697, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122697, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40055 q ha hb
  have h2 (q : Pattern) (ha : d122698 q = 1) (hb : d163491 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122698, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122698, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122699 q = 1) (hb : d163492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122699, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122699, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122700 q = 1) (hb : d163493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122700, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122700, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122701 q = 1) (hb : d163494 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122701, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122701, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122702 q = 1) (hb : d163495 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122702, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122702, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40057 (p : Pattern) (ha : d14497 p = 1) (hb : d122797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14492 q = 1) (hb : d122729 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39807 q ha hb
    | true =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39808 q ha hb
  have h5 (q : Pattern) (ha : d14493 q = 1) (hb : d122787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d122787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14493, d122787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14494 q = 1) (hb : d122794 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d122794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14494, d122794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14495 q = 1) (hb : d122795 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d122795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14495, d122795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14496 q = 1) (hb : d122796 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d122796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14496, d122796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14497 q = 1) (hb : d122797 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d122797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, d122797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40058 (p : Pattern) (ha : d14507 p = 1) (hb : d122818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14492 q = 1) (hb : d122729 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39807 q ha hb
    | true =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39808 q ha hb
  have h4 (q : Pattern) (ha : d14493 q = 1) (hb : d122787 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d122787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14493, d122787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d122793 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14494 q = 1) (hb : d122794 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d122794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14494, d122794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14495 q = 1) (hb : d122795 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d122795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14495, d122795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14496 q = 1) (hb : d122796 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d122796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d122796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122803 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d122808 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14502 q = 1) (hb : d122739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d122739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39810 q ha hb
    | true =>
      simp only [d14502, d122739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39811 q ha hb
  have h13 (q : Pattern) (ha : d14503 q = 1) (hb : d122811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d122811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14503, d122811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14504 q = 1) (hb : d122815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d122815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14504, d122815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14505 q = 1) (hb : d122816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d122816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14505, d122816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14506 q = 1) (hb : d122817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d122817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14506, d122817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14507 q = 1) (hb : d122818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d122818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14507, d122818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40059 (p : Pattern) (ha : d122838 p = 1) (hb : d163499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14502 q = 1) (hb : d122739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d122739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39810 q ha hb
    | true =>
      simp only [d14502, d122739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39811 q ha hb
  have h3 (q : Pattern) (ha : d14503 q = 1) (hb : d122811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d122811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14503, d122811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122814 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14504 q = 1) (hb : d122815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d122815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14504, d122815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14505 q = 1) (hb : d122836 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d122836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d122836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14506 q = 1) (hb : d122837 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d122837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d122837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122838 q = 1) (hb : d163499 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122838, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122838, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40060 (p : Pattern) (ha : d122906 p = 1) (hb : d163510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122895 q = 1) (hb : d163505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d122895, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39843 q hb ha
    | true =>
      simp only [d122895, d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39818 q hb ha
  have h3 (q : Pattern) (ha : d122896 q = 1) (hb : d163506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d122896, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122896, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122903 q = 1) (hb : d163507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d122903, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122903, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122904 q = 1) (hb : d163508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d122904, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122904, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122905 q = 1) (hb : d163509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d122905, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122905, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122906 q = 1) (hb : d163510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d122906, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122906, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40061 (p : Pattern) (ha : d122919 p = 1) (hb : d163516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d122819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d122819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40057 q ha hb
    | true =>
      simp only [d14508, d122819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40058 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d122832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14509 q = 1) (hb : d122833 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d122833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, d122833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122834 q = 1) (hb : d163497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122834, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d122834, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122835 q = 1) (hb : d163498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122835, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122835, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122839 q = 1) (hb : d163500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122839, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122839, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40059 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d122841 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d122842 q = 1) (hb : d163501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122842, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d122842, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122843 q = 1) (hb : d163502 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122843, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d122843, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122844 q = 1) (hb : d163503 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122844, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d122844, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d122845 q = 1) (hb : d163504 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122845, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122845, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122907 q = 1) (hb : d163511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d122907, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d122907, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40060 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d122914 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d122915 q = 1) (hb : d163512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d122915, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d122915, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d122916 q = 1) (hb : d163513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d122916, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d122916, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122917 q = 1) (hb : d163514 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d122917, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d122917, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d122918 q = 1) (hb : d163515 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d122918, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d122918, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d122919 q = 1) (hb : d163516 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d122919, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d122919, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40062 (p : Pattern) (ha : d122925 p = 1) (hb : d163522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122920 q = 1) (hb : d163517 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d122920, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122920, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40061 q ha hb
  have h2 (q : Pattern) (ha : d122921 q = 1) (hb : d163518 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d122921, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122921, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122922 q = 1) (hb : d163519 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d122922, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122922, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122923 q = 1) (hb : d163520 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d122923, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122923, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122924 q = 1) (hb : d163521 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d122924, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122924, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122925 q = 1) (hb : d163522 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d122925, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d122925, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40063 (p : Pattern) (ha : d14804 p = 1) (hb : d123056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14799 q = 1) (hb : d122970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d122970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39852 q ha hb
    | true =>
      simp only [d14799, d122970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39853 q ha hb
  have h5 (q : Pattern) (ha : d14800 q = 1) (hb : d123038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d123038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14800, d123038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14801 q = 1) (hb : d123053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d123053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14801, d123053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14802 q = 1) (hb : d123054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d123054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14802, d123054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14803 q = 1) (hb : d123055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d123055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14803, d123055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14804 q = 1) (hb : d123056 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, d123056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, d123056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40064 (p : Pattern) (ha : d14814 p = 1) (hb : d123078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122996 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14799 q = 1) (hb : d122970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d122970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39852 q ha hb
    | true =>
      simp only [d14799, d122970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39853 q ha hb
  have h4 (q : Pattern) (ha : d14800 q = 1) (hb : d123038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d123038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14800, d123038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123052 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14801 q = 1) (hb : d123053 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d123053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14801, d123053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14802 q = 1) (hb : d123054 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d123054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14802, d123054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14803 q = 1) (hb : d123055 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d123055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d123055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123062 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123067 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d14809 q = 1) (hb : d122980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d122980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39855 q ha hb
    | true =>
      simp only [d14809, d122980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39856 q ha hb
  have h13 (q : Pattern) (ha : d14810 q = 1) (hb : d123071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d123071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14810, d123071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14811 q = 1) (hb : d123075 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d123075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14811, d123075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14812 q = 1) (hb : d123076 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d123076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14812, d123076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14813 q = 1) (hb : d123077 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d123077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14813, d123077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14814 q = 1) (hb : d123078 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, d123078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14814, d123078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40065 (p : Pattern) (ha : d123103 p = 1) (hb : d163527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14809 q = 1) (hb : d122980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d122980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39855 q ha hb
    | true =>
      simp only [d14809, d122980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39856 q ha hb
  have h3 (q : Pattern) (ha : d14810 q = 1) (hb : d123071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d123071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14810, d123071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123074 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14811 q = 1) (hb : d123075 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d123075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14811, d123075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14812 q = 1) (hb : d123101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d123101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d123101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14813 q = 1) (hb : d123102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d123102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d123102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123103 q = 1) (hb : d163527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123103, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123103, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40066 (p : Pattern) (ha : d123182 p = 1) (hb : d163534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d123141 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d123141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39888 q ha hb
    | true =>
      simp only [d15016, d123141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39863 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d123142 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d123142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d123142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d123143 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d123143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d123143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d123150 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d123150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39863 q ha hb
    | true =>
      simp only [d15025, d123150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33885 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d123151 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d123151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d123151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d123152 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d123152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d123152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d123153 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d123153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d123153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15043 q = 1) (hb : d123168 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d123168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39863 q ha hb
    | true =>
      simp only [d15043, d123168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33858 q ha hb
  have h9 (q : Pattern) (ha : d15044 q = 1) (hb : d123169 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d123169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d123169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15045 q = 1) (hb : d123170 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d123170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d123170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15046 q = 1) (hb : d123171 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d123171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15046, d123171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d123181 q = 1) (hb : d163533 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123181, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123181, d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123182 q = 1) (hb : d163534 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123182, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123182, d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40067 (p : Pattern) (ha : d123188 p = 1) (hb : d163540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123183 q = 1) (hb : d163535 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123183, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40066 q ha hb
    | true =>
      simp only [d123183, d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123184 q = 1) (hb : d163536 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123184, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123184, d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d123174 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d123174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39864 q ha hb
    | true =>
      simp only [d15049, d123174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d123175 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d123175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d123175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123185 q = 1) (hb : d163537 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123185, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123185, d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123186 q = 1) (hb : d163538 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123186, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123186, d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123187 q = 1) (hb : d163539 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123187, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123187, d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123188 q = 1) (hb : d163540 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123188, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123188, d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40068 (p : Pattern) (ha : d123212 p = 1) (hb : d163546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123180 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123193 q = 1) (hb : d163541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123193, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40067 q ha hb
    | true =>
      simp only [d123193, d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39865 q hb ha
  have h3 (q : Pattern) (ha : d123194 q = 1) (hb : d163542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123194, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123194, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123208 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123209 q = 1) (hb : d163543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123209, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123209, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123210 q = 1) (hb : d163544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123210, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123210, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123211 q = 1) (hb : d163545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123211, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123211, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123212 q = 1) (hb : d163546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123212, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123212, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40069 (p : Pattern) (ha : d123225 p = 1) (hb : d163552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d123079 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d123079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40063 q ha hb
    | true =>
      simp only [d14815, d123079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40064 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14816 q = 1) (hb : d123098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d123098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, d123098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123099 q = 1) (hb : d163525 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123099, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123099, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123100 q = 1) (hb : d163526 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123100, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123100, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123104 q = 1) (hb : d163528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123104, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123104, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40065 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123106 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123107 q = 1) (hb : d163529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123107, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123107, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123108 q = 1) (hb : d163530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123108, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123108, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123109 q = 1) (hb : d163531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123109, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123109, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123110 q = 1) (hb : d163532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123110, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123110, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123213 q = 1) (hb : d163547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123213, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123213, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40068 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123220 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123221 q = 1) (hb : d163548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123221, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123221, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123222 q = 1) (hb : d163549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123222, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123222, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123223 q = 1) (hb : d163550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123223, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123223, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123224 q = 1) (hb : d163551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123224, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123224, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123225 q = 1) (hb : d163552 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123225, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123225, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40070 (p : Pattern) (ha : d123231 p = 1) (hb : d163558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123226 q = 1) (hb : d163553 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123226, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123226, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40069 q ha hb
  have h2 (q : Pattern) (ha : d123227 q = 1) (hb : d163554 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123227, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123227, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123228 q = 1) (hb : d163555 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123228, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123228, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123229 q = 1) (hb : d163556 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123229, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123229, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123230 q = 1) (hb : d163557 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123230, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123230, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123231 q = 1) (hb : d163558 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123231, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123231, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40071 (p : Pattern) (ha : d15197 p = 1) (hb : d123363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15192 q = 1) (hb : d123277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d123277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39903 q ha hb
    | true =>
      simp only [d15192, d123277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39904 q ha hb
  have h5 (q : Pattern) (ha : d15193 q = 1) (hb : d123345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d123345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15193, d123345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15194 q = 1) (hb : d123360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d123360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15194, d123360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15195 q = 1) (hb : d123361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d123361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15195, d123361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15196 q = 1) (hb : d123362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d123362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15196, d123362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15197 q = 1) (hb : d123363 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d123363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d123363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40072 (p : Pattern) (ha : d15207 p = 1) (hb : d123385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123303 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15192 q = 1) (hb : d123277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d123277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39903 q ha hb
    | true =>
      simp only [d15192, d123277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39904 q ha hb
  have h4 (q : Pattern) (ha : d15193 q = 1) (hb : d123345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d123345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15193, d123345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123359 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15194 q = 1) (hb : d123360 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d123360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15194, d123360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15195 q = 1) (hb : d123361 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d123361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15195, d123361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15196 q = 1) (hb : d123362 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d123362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d123362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123369 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123374 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15202 q = 1) (hb : d123287 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d123287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39906 q ha hb
    | true =>
      simp only [d15202, d123287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39907 q ha hb
  have h13 (q : Pattern) (ha : d15203 q = 1) (hb : d123378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d123378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15203, d123378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15204 q = 1) (hb : d123382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d123382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15204, d123382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15205 q = 1) (hb : d123383 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d123383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15205, d123383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15206 q = 1) (hb : d123384 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d123384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15206, d123384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15207 q = 1) (hb : d123385 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d123385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15207, d123385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40073 (p : Pattern) (ha : d123410 p = 1) (hb : d163564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15202 q = 1) (hb : d123287 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d123287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39906 q ha hb
    | true =>
      simp only [d15202, d123287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39907 q ha hb
  have h3 (q : Pattern) (ha : d15203 q = 1) (hb : d123378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d123378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15203, d123378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15204 q = 1) (hb : d123382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d123382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15204, d123382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15205 q = 1) (hb : d123408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d123408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d123408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15206 q = 1) (hb : d123409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d123409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d123409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123410 q = 1) (hb : d163564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123410, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123410, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40074 (p : Pattern) (ha : d123489 p = 1) (hb : d163571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d123448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d123448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39939 q ha hb
    | true =>
      simp only [d15409, d123448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39914 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d123449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d123449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d123449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d123450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d123450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d123450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d123457 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d123457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39914 q ha hb
    | true =>
      simp only [d15418, d123457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33938 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d123458 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d123458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d123458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d123459 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d123459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d123459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d123460 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d123460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d123460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15436 q = 1) (hb : d123475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d123475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39914 q ha hb
    | true =>
      simp only [d15436, d123475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33911 q ha hb
  have h9 (q : Pattern) (ha : d15437 q = 1) (hb : d123476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d123476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d123476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15438 q = 1) (hb : d123477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d123477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d123477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15439 q = 1) (hb : d123478 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d123478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15439, d123478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d123488 q = 1) (hb : d163570 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123488, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123488, d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123489 q = 1) (hb : d163571 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123489, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123489, d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40075 (p : Pattern) (ha : d123495 p = 1) (hb : d163577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123490 q = 1) (hb : d163572 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123490, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40074 q ha hb
    | true =>
      simp only [d123490, d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123491 q = 1) (hb : d163573 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123491, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123491, d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d123481 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d123481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39915 q ha hb
    | true =>
      simp only [d15442, d123481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d123482 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d123482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d123482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123492 q = 1) (hb : d163574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123492, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123492, d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123493 q = 1) (hb : d163575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123493, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123493, d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123494 q = 1) (hb : d163576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123494, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123494, d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123495 q = 1) (hb : d163577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123495, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123495, d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40076 (p : Pattern) (ha : d123519 p = 1) (hb : d163583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123500 q = 1) (hb : d163578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123500, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40075 q ha hb
    | true =>
      simp only [d123500, d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39916 q hb ha
  have h3 (q : Pattern) (ha : d123501 q = 1) (hb : d163579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123501, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123501, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123516 q = 1) (hb : d163580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123516, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123516, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123517 q = 1) (hb : d163581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123517, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123517, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123518 q = 1) (hb : d163582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123518, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123518, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123519 q = 1) (hb : d163583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123519, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123519, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40077 (p : Pattern) (ha : d123532 p = 1) (hb : d163589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d123386 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d123386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40071 q ha hb
    | true =>
      simp only [d15208, d123386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40072 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15209 q = 1) (hb : d123405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d123405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, d123405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123406 q = 1) (hb : d163562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123406, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123406, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123407 q = 1) (hb : d163563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123407, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123407, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123411 q = 1) (hb : d163565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123411, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123411, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40073 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123413 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123414 q = 1) (hb : d163566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123414, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123414, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123415 q = 1) (hb : d163567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123415, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123415, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123416 q = 1) (hb : d163568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123416, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123416, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123417 q = 1) (hb : d163569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123417, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123417, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123520 q = 1) (hb : d163584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123520, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123520, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40076 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123527 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123528 q = 1) (hb : d163585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123528, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123528, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123529 q = 1) (hb : d163586 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123529, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123529, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123530 q = 1) (hb : d163587 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123530, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123530, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123531 q = 1) (hb : d163588 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123531, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123531, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123532 q = 1) (hb : d163589 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123532, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123532, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40078 (p : Pattern) (ha : d123538 p = 1) (hb : d163595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123533 q = 1) (hb : d163590 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123533, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123533, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40077 q ha hb
  have h2 (q : Pattern) (ha : d123534 q = 1) (hb : d163591 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123534, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123534, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123535 q = 1) (hb : d163592 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123535, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123535, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123536 q = 1) (hb : d163593 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123536, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123536, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123537 q = 1) (hb : d163594 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123537, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123537, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123538 q = 1) (hb : d163595 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123538, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123538, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40079 (p : Pattern) (ha : d15589 p = 1) (hb : d123665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15584 q = 1) (hb : d123583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d123583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39954 q ha hb
    | true =>
      simp only [d15584, d123583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39955 q ha hb
  have h5 (q : Pattern) (ha : d15585 q = 1) (hb : d123647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d123647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15585, d123647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15586 q = 1) (hb : d123662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d123662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15586, d123662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15587 q = 1) (hb : d123663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d123663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15587, d123663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15588 q = 1) (hb : d123664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d123664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15588, d123664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15589 q = 1) (hb : d123665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d123665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d123665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40080 (p : Pattern) (ha : d15599 p = 1) (hb : d123687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123609 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123618 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123646 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15584 q = 1) (hb : d123583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d123583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39954 q ha hb
    | true =>
      simp only [d15584, d123583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39955 q ha hb
  have h4 (q : Pattern) (ha : d15585 q = 1) (hb : d123647 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d123647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15585, d123647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d123661 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15586 q = 1) (hb : d123662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d123662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15586, d123662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15587 q = 1) (hb : d123663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d123663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15587, d123663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15588 q = 1) (hb : d123664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d123664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d123664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d123676 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15594 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d123593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39957 q ha hb
    | true =>
      simp only [d15594, d123593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39958 q ha hb
  have h13 (q : Pattern) (ha : d15595 q = 1) (hb : d123680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d123680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15595, d123680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15596 q = 1) (hb : d123684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d123684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15596, d123684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15597 q = 1) (hb : d123685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d123685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15597, d123685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15598 q = 1) (hb : d123686 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d123686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15598, d123686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15599 q = 1) (hb : d123687 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d123687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15599, d123687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40081 (p : Pattern) (ha : d123712 p = 1) (hb : d163602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123679 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15594 q = 1) (hb : d123593 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d123593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39957 q ha hb
    | true =>
      simp only [d15594, d123593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39958 q ha hb
  have h3 (q : Pattern) (ha : d15595 q = 1) (hb : d123680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d123680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15595, d123680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123683 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15596 q = 1) (hb : d123684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d123684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15596, d123684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15597 q = 1) (hb : d123710 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d123710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d123710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15598 q = 1) (hb : d123711 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d123711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d123711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123712 q = 1) (hb : d163602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123712, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123712, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40082 (p : Pattern) (ha : d123781 p = 1) (hb : d163609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d123740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d123740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39988 q ha hb
    | true =>
      simp only [d15787, d123740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39965 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d123741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d123741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d123741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d123742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d123742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d123742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d123749 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d123749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39965 q ha hb
    | true =>
      simp only [d15796, d123749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33991 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d123750 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d123750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d123750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d123751 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d123751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d123751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d123752 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d123752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d123752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15814 q = 1) (hb : d123767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d123767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39965 q ha hb
    | true =>
      simp only [d15814, d123767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33964 q ha hb
  have h9 (q : Pattern) (ha : d15815 q = 1) (hb : d123768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d123768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d123768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15816 q = 1) (hb : d123769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d123769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d123769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15817 q = 1) (hb : d123770 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d123770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15817, d123770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d123780 q = 1) (hb : d163608 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d123780, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d123780, d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123781 q = 1) (hb : d163609 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d123781, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123781, d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro40083 (p : Pattern) (ha : d123787 p = 1) (hb : d163615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123782 q = 1) (hb : d163610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d123782, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40082 q ha hb
    | true =>
      simp only [d123782, d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123783 q = 1) (hb : d163611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d123783, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123783, d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d123773 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d123773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39966 q ha hb
    | true =>
      simp only [d15820, d123773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d123774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d123774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d123774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123784 q = 1) (hb : d163612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d123784, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123784, d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123785 q = 1) (hb : d163613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d123785, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123785, d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d123786 q = 1) (hb : d163614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d123786, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123786, d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d123787 q = 1) (hb : d163615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123787, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123787, d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro40084 (p : Pattern) (ha : d123811 p = 1) (hb : d163621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d123779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d123792 q = 1) (hb : d163616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d123792, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40083 q ha hb
    | true =>
      simp only [d123792, d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39967 q hb ha
  have h3 (q : Pattern) (ha : d123793 q = 1) (hb : d163617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d123793, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123793, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d123807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123808 q = 1) (hb : d163618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d123808, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123808, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123809 q = 1) (hb : d163619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d123809, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123809, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123810 q = 1) (hb : d163620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d123810, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123810, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d123811 q = 1) (hb : d163621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d123811, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123811, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40085 (p : Pattern) (ha : d123824 p = 1) (hb : d163627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d123601 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d123688 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d123688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40079 q ha hb
    | true =>
      simp only [d15600, d123688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40080 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d123706 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15601 q = 1) (hb : d123707 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d123707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, d123707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d123708 q = 1) (hb : d163600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123708, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d123708, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d123709 q = 1) (hb : d163601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123709, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123709, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123713 q = 1) (hb : d163603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123713, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123713, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40081 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123715 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d123716 q = 1) (hb : d163604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123716, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123716, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d123717 q = 1) (hb : d163605 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123717, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d123717, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d123718 q = 1) (hb : d163606 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123718, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123718, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d123719 q = 1) (hb : d163607 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123719, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123719, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123812 q = 1) (hb : d163622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d123812, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d123812, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40084 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d123819 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d123820 q = 1) (hb : d163623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d123820, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123820, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d123821 q = 1) (hb : d163624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d123821, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123821, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d123822 q = 1) (hb : d163625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d123822, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d123822, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d123823 q = 1) (hb : d163626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d123823, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d123823, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d123824 q = 1) (hb : d163627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d123824, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123824, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40086 (p : Pattern) (ha : d123830 p = 1) (hb : d163633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123825 q = 1) (hb : d163628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d123825, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123825, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40085 q ha hb
  have h2 (q : Pattern) (ha : d123826 q = 1) (hb : d163629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d123826, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123826, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d123827 q = 1) (hb : d163630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d123827, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123827, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123828 q = 1) (hb : d163631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d123828, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123828, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d123829 q = 1) (hb : d163632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d123829, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123829, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123830 q = 1) (hb : d163633 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d123830, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d123830, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40087 (p : Pattern) (ha : d123836 p = 1) (hb : d163639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d122703 q = 1) (hb : d163496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122703, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40050 q ha hb
    | true =>
      simp only [d122703, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40056 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122926 q = 1) (hb : d163523 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d122926, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d122926, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40062 q ha hb
  have h3 (q : Pattern) (ha : d122927 q = 1) (hb : d163524 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d122927, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d122927, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d123232 q = 1) (hb : d163559 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123232, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123232, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40070 q ha hb
  have h5 (q : Pattern) (ha : d123233 q = 1) (hb : d163560 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123233, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123233, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123234 q = 1) (hb : d163561 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123234, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123234, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d123539 q = 1) (hb : d163596 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123539, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123539, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40078 q ha hb
  have h8 (q : Pattern) (ha : d123540 q = 1) (hb : d163597 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123540, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123540, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d123541 q = 1) (hb : d163598 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123541, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123541, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d123542 q = 1) (hb : d163599 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123542, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d123542, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d123831 q = 1) (hb : d163634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d123831, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123831, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40086 q ha hb
  have h12 (q : Pattern) (ha : d123832 q = 1) (hb : d163635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d123832, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123832, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d123833 q = 1) (hb : d163636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d123833, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123833, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123834 q = 1) (hb : d163637 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d123834, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d123834, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d123835 q = 1) (hb : d163638 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d123835, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d123835, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d123836 q = 1) (hb : d163639 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d123836, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d123836, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro40088 (p : Pattern) (ha : d123842 p = 1) (hb : d163645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123837 q = 1) (hb : d163640 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d123837, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40087 q ha hb
    | true =>
      simp only [d123837, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123838 q = 1) (hb : d163641 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d123838, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123838, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123839 q = 1) (hb : d163642 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d123839, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123839, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123840 q = 1) (hb : d163643 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d123840, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123840, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123841 q = 1) (hb : d163644 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d123841, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123841, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123842 q = 1) (hb : d163645 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d123842, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123842, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40089 (p : Pattern) (ha : d123848 p = 1) (hb : d163651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123843 q = 1) (hb : d163646 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d123843, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40088 q ha hb
    | true =>
      simp only [d123843, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123844 q = 1) (hb : d163647 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d123844, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123844, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123845 q = 1) (hb : d163648 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d123845, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123845, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123846 q = 1) (hb : d163649 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d123846, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123846, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123847 q = 1) (hb : d163650 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d123847, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123847, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123848 q = 1) (hb : d163651 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d123848, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123848, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40090 (p : Pattern) (ha : d123854 p = 1) (hb : d163657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123849 q = 1) (hb : d163652 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d123849, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40089 q ha hb
    | true =>
      simp only [d123849, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123850 q = 1) (hb : d163653 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d123850, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123850, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123851 q = 1) (hb : d163654 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d123851, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123851, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123852 q = 1) (hb : d163655 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d123852, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123852, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123853 q = 1) (hb : d163656 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d123853, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123853, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123854 q = 1) (hb : d163657 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d123854, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123854, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40091 (p : Pattern) (ha : d123860 p = 1) (hb : d163663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123855 q = 1) (hb : d163658 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d123855, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40090 q ha hb
    | true =>
      simp only [d123855, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123856 q = 1) (hb : d163659 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d123856, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123856, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123857 q = 1) (hb : d163660 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d123857, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123857, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123858 q = 1) (hb : d163661 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d123858, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123858, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123859 q = 1) (hb : d163662 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d123859, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123859, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123860 q = 1) (hb : d163663 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d123860, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123860, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40092 (p : Pattern) (ha : d123866 p = 1) (hb : d163669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123861 q = 1) (hb : d163664 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d123861, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40091 q ha hb
    | true =>
      simp only [d123861, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123862 q = 1) (hb : d163665 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d123862, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123862, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123863 q = 1) (hb : d163666 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d123863, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123863, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123864 q = 1) (hb : d163667 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d123864, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123864, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123865 q = 1) (hb : d163668 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d123865, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123865, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123866 q = 1) (hb : d163669 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d123866, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123866, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40093 (p : Pattern) (ha : d123872 p = 1) (hb : d163675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123867 q = 1) (hb : d163670 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d123867, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40092 q ha hb
    | true =>
      simp only [d123867, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123868 q = 1) (hb : d163671 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d123868, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123868, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123869 q = 1) (hb : d163672 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d123869, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123869, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123870 q = 1) (hb : d163673 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d123870, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123870, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123871 q = 1) (hb : d163674 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d123871, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123871, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123872 q = 1) (hb : d163675 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d123872, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123872, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40094 (p : Pattern) (ha : d123878 p = 1) (hb : d163681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d123873 q = 1) (hb : d163676 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d123873, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40093 q ha hb
    | true =>
      simp only [d123873, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d123874 q = 1) (hb : d163677 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d123874, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d123874, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d123875 q = 1) (hb : d163678 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d123875, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d123875, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d123876 q = 1) (hb : d163679 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d123876, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d123876, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d123877 q = 1) (hb : d163680 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d123877, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d123877, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d123878 q = 1) (hb : d163681 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d123878, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d123878, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro40095 (p : Pattern) (ha : d14054 p = 1) (hb : d125455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14050 q = 1) (hb : d125451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14050, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14051 q = 1) (hb : d125452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14051, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14052 q = 1) (hb : d125453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14052, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14053 q = 1) (hb : d125454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14053, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14054 q = 1) (hb : d125455 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40096 (p : Pattern) (ha : d14061 p = 1) (hb : d125460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14070 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14076 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14092 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13994 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14050 q = 1) (hb : d125451 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14050, d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14051 q = 1) (hb : d125452 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14051, d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14052 q = 1) (hb : d125453 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14052, d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14053 q = 1) (hb : d125454 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14123 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14127 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14001 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14057 q = 1) (hb : d125456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14057, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14058 q = 1) (hb : d125457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14058, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14059 q = 1) (hb : d125458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14059, d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14060 q = 1) (hb : d125459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14060, d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14061 q = 1) (hb : d125460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14061, d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40097 (p : Pattern) (ha : d125467 p = 1) (hb : d163447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14001 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14057 q = 1) (hb : d125456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14057, d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14135 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14058 q = 1) (hb : d125457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14058, d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14059 q = 1) (hb : d125465 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14060 q = 1) (hb : d125466 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125467 q = 1) (hb : d163447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125467, d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40098 (p : Pattern) (ha : d125477 p = 1) (hb : d163457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14169 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125473 q = 1) (hb : d163453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125473, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125473, d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14191 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125474 q = 1) (hb : d163454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125474, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125474, d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125475 q = 1) (hb : d163455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125475, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125475, d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125476 q = 1) (hb : d163456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125476, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125476, d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125477 q = 1) (hb : d163457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125477, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125477, d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40099 (p : Pattern) (ha : d125483 p = 1) (hb : d163463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14064 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d125461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40095 q ha hb
    | true =>
      simp only [d14062, d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40096 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14063 q = 1) (hb : d125462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125463 q = 1) (hb : d163445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125463, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125463, d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125464 q = 1) (hb : d163446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125464, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125464, d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125468 q = 1) (hb : d163448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125468, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125468, d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40097 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125469 q = 1) (hb : d163449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125469, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125469, d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125470 q = 1) (hb : d163450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125470, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125470, d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125471 q = 1) (hb : d163451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125471, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125471, d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125472 q = 1) (hb : d163452 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125472, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125472, d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125478 q = 1) (hb : d163458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125478, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125478, d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40098 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125479 q = 1) (hb : d163459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125479, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125479, d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125480 q = 1) (hb : d163460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125480, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125480, d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125481 q = 1) (hb : d163461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125481, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125481, d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125482 q = 1) (hb : d163462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125482, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125482, d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125483 q = 1) (hb : d163463 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125483, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125483, d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40100 (p : Pattern) (ha : d125489 p = 1) (hb : d163469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d125446 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22508 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d125447 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d125448 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d125449 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d125450 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125484 q = 1) (hb : d163464 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125484, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125484, d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40099 q ha hb
  have h8 (q : Pattern) (ha : d125485 q = 1) (hb : d163465 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125485, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125485, d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125486 q = 1) (hb : d163466 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125486, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125486, d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125487 q = 1) (hb : d163467 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125487, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125487, d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125488 q = 1) (hb : d163468 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125488, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125488, d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d125489 q = 1) (hb : d163469 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125489, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d125489, d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro40101 (p : Pattern) (ha : d14230 p = 1) (hb : d125494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14225 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14226 q = 1) (hb : d125490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14226, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14227 q = 1) (hb : d125491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14227, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14228 q = 1) (hb : d125492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14228, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14229 q = 1) (hb : d125493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14229, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14230 q = 1) (hb : d125494 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40102 (p : Pattern) (ha : d14240 p = 1) (hb : d125499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14251 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14260 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14280 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14225 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14226 q = 1) (hb : d125490 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14226, d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14314 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14227 q = 1) (hb : d125491 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14227, d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14228 q = 1) (hb : d125492 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14228, d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14229 q = 1) (hb : d125493 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14324 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14235 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14236 q = 1) (hb : d125495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14236, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14237 q = 1) (hb : d125496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14237, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14238 q = 1) (hb : d125497 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14238, d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14239 q = 1) (hb : d125498 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14239, d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14240 q = 1) (hb : d125499 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14240, d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40103 (p : Pattern) (ha : d125506 p = 1) (hb : d163472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14235 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14236 q = 1) (hb : d125495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14236, d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14338 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14237 q = 1) (hb : d125496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14237, d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14238 q = 1) (hb : d125504 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14239 q = 1) (hb : d125505 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125506 q = 1) (hb : d163472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125506, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125506, d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40104 (p : Pattern) (ha : d125516 p = 1) (hb : d163483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14402 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125512 q = 1) (hb : d163479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125512, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125512, d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14438 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125513 q = 1) (hb : d163480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125513, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125513, d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125514 q = 1) (hb : d163481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125514, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125514, d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125515 q = 1) (hb : d163482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125515, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125515, d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125516 q = 1) (hb : d163483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125516, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125516, d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40105 (p : Pattern) (ha : d125522 p = 1) (hb : d163489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14243 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d125500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40101 q ha hb
    | true =>
      simp only [d14241, d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40102 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14242 q = 1) (hb : d125501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125502 q = 1) (hb : d163470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125502, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125502, d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125503 q = 1) (hb : d163471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125503, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125503, d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125507 q = 1) (hb : d163473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125507, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125507, d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40103 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14365 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125508 q = 1) (hb : d163474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125508, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125508, d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125509 q = 1) (hb : d163475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125509, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125509, d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125510 q = 1) (hb : d163476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125510, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125510, d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125511 q = 1) (hb : d163477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125511, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125511, d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125517 q = 1) (hb : d163484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125517, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125517, d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40104 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14454 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125518 q = 1) (hb : d163485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125518, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125518, d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125519 q = 1) (hb : d163486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125519, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125519, d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125520 q = 1) (hb : d163487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125520, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125520, d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125521 q = 1) (hb : d163488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125521, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125521, d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125522 q = 1) (hb : d163489 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125522, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125522, d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40106 (p : Pattern) (ha : d125528 p = 1) (hb : d163495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125523 q = 1) (hb : d163490 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125523, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125523, d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40105 q ha hb
  have h2 (q : Pattern) (ha : d125524 q = 1) (hb : d163491 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125524, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125524, d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125525 q = 1) (hb : d163492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125525, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125525, d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125526 q = 1) (hb : d163493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125526, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125526, d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125527 q = 1) (hb : d163494 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125527, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125527, d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125528 q = 1) (hb : d163495 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125528, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125528, d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40107 (p : Pattern) (ha : d14497 p = 1) (hb : d125534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14492 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14493 q = 1) (hb : d125530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14493, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14494 q = 1) (hb : d125531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14494, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14495 q = 1) (hb : d125532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14495, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14496 q = 1) (hb : d125533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14496, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14497 q = 1) (hb : d125534 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40108 (p : Pattern) (ha : d14507 p = 1) (hb : d125539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14493 q = 1) (hb : d125530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14493, d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14494 q = 1) (hb : d125531 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14494, d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14495 q = 1) (hb : d125532 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14495, d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14496 q = 1) (hb : d125533 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14502 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14503 q = 1) (hb : d125535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14503, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14504 q = 1) (hb : d125536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14504, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14505 q = 1) (hb : d125537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14505, d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14506 q = 1) (hb : d125538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14506, d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14507 q = 1) (hb : d125539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14507, d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40109 (p : Pattern) (ha : d125546 p = 1) (hb : d163499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14604 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14503 q = 1) (hb : d125535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14503, d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14611 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14504 q = 1) (hb : d125536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14504, d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14505 q = 1) (hb : d125544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14506 q = 1) (hb : d125545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125546 q = 1) (hb : d163499 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125546, d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40110 (p : Pattern) (ha : d125556 p = 1) (hb : d163510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125552 q = 1) (hb : d163506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125552, d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14727 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125553 q = 1) (hb : d163507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125553, d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125554 q = 1) (hb : d163508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125554, d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125555 q = 1) (hb : d163509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125555, d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125556 q = 1) (hb : d163510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125556, d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40111 (p : Pattern) (ha : d125562 p = 1) (hb : d163516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d125540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40107 q ha hb
    | true =>
      simp only [d14508, d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14509 q = 1) (hb : d125541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125542 q = 1) (hb : d163497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125542, d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125543 q = 1) (hb : d163498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125543, d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125547 q = 1) (hb : d163500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125547, d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40109 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14638 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125548 q = 1) (hb : d163501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125548, d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125549 q = 1) (hb : d163502 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125549, d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125550 q = 1) (hb : d163503 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125550, d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125551 q = 1) (hb : d163504 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125551, d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125557 q = 1) (hb : d163511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125557, d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40110 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14743 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125558 q = 1) (hb : d163512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125558, d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125559 q = 1) (hb : d163513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125559, d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125560 q = 1) (hb : d163514 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125560, d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125561 q = 1) (hb : d163515 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125561, d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125562 q = 1) (hb : d163516 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125562, d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40112 (p : Pattern) (ha : d125568 p = 1) (hb : d163522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125563 q = 1) (hb : d163517 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125563, d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40111 q ha hb
  have h2 (q : Pattern) (ha : d125564 q = 1) (hb : d163518 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125564, d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125565 q = 1) (hb : d163519 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125565, d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125566 q = 1) (hb : d163520 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125566, d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125567 q = 1) (hb : d163521 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125567, d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125568 q = 1) (hb : d163522 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125568, d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40113 (p : Pattern) (ha : d14804 p = 1) (hb : d125575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14799 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14800 q = 1) (hb : d125571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14800, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14801 q = 1) (hb : d125572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14801, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14802 q = 1) (hb : d125573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14802, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14803 q = 1) (hb : d125574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14803, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14804 q = 1) (hb : d125575 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40114 (p : Pattern) (ha : d14814 p = 1) (hb : d125580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14799 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14800 q = 1) (hb : d125571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14800, d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14924 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14801 q = 1) (hb : d125572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14801, d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14802 q = 1) (hb : d125573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14802, d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14803 q = 1) (hb : d125574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14934 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14939 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d14809 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14810 q = 1) (hb : d125576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14810, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14811 q = 1) (hb : d125577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14811, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14812 q = 1) (hb : d125578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14812, d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14813 q = 1) (hb : d125579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14813, d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14814 q = 1) (hb : d125580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14814, d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40115 (p : Pattern) (ha : d125587 p = 1) (hb : d163527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14810 q = 1) (hb : d125576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14810, d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14949 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14811 q = 1) (hb : d125577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14811, d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14812 q = 1) (hb : d125585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14813 q = 1) (hb : d125586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125587 q = 1) (hb : d163527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125587, d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40116 (p : Pattern) (ha : d125597 p = 1) (hb : d163546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163541 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125593 q = 1) (hb : d163542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125593, d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125594 q = 1) (hb : d163543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125594, d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125595 q = 1) (hb : d163544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125595, d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125596 q = 1) (hb : d163545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125596, d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125597 q = 1) (hb : d163546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125597, d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40117 (p : Pattern) (ha : d125603 p = 1) (hb : d163552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d125581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40113 q ha hb
    | true =>
      simp only [d14815, d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40114 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14972 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14816 q = 1) (hb : d125582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125583 q = 1) (hb : d163525 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125583, d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125584 q = 1) (hb : d163526 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125584, d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125588 q = 1) (hb : d163528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125588, d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40115 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14981 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125589 q = 1) (hb : d163529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125589, d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125590 q = 1) (hb : d163530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125590, d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125591 q = 1) (hb : d163531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125591, d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125592 q = 1) (hb : d163532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125592, d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125598 q = 1) (hb : d163547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125598, d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40116 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125599 q = 1) (hb : d163548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125599, d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125600 q = 1) (hb : d163549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125600, d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125601 q = 1) (hb : d163550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125601, d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125602 q = 1) (hb : d163551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125602, d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125603 q = 1) (hb : d163552 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125603, d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40118 (p : Pattern) (ha : d125609 p = 1) (hb : d163558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125604 q = 1) (hb : d163553 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125604, d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40117 q ha hb
  have h2 (q : Pattern) (ha : d125605 q = 1) (hb : d163554 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125605, d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125606 q = 1) (hb : d163555 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125606, d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125607 q = 1) (hb : d163556 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125607, d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125608 q = 1) (hb : d163557 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125608, d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125609 q = 1) (hb : d163558 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125609, d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40119 (p : Pattern) (ha : d15197 p = 1) (hb : d125617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15192 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15193 q = 1) (hb : d125613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15193, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15194 q = 1) (hb : d125614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15194, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15195 q = 1) (hb : d125615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15195, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15196 q = 1) (hb : d125616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15196, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15197 q = 1) (hb : d125617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40120 (p : Pattern) (ha : d15207 p = 1) (hb : d125622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15227 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15192 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15193 q = 1) (hb : d125613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15193, d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15194 q = 1) (hb : d125614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15194, d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15195 q = 1) (hb : d125615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15195, d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15196 q = 1) (hb : d125616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d15202 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15203 q = 1) (hb : d125618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15203, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15204 q = 1) (hb : d125619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15204, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15205 q = 1) (hb : d125620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15205, d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15206 q = 1) (hb : d125621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15206, d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15207 q = 1) (hb : d125622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15207, d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40121 (p : Pattern) (ha : d125629 p = 1) (hb : d163564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15202 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15203 q = 1) (hb : d125618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15203, d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15204 q = 1) (hb : d125619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15204, d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15205 q = 1) (hb : d125627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15206 q = 1) (hb : d125628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125629 q = 1) (hb : d163564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125629, d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40122 (p : Pattern) (ha : d125639 p = 1) (hb : d163583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125635 q = 1) (hb : d163579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125635, d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15512 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125636 q = 1) (hb : d163580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125636, d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125637 q = 1) (hb : d163581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125637, d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125638 q = 1) (hb : d163582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125638, d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125639 q = 1) (hb : d163583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125639, d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40123 (p : Pattern) (ha : d125645 p = 1) (hb : d163589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15210 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d125623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40119 q ha hb
    | true =>
      simp only [d15208, d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40120 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15365 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15209 q = 1) (hb : d125624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125625 q = 1) (hb : d163562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125625, d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125626 q = 1) (hb : d163563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125626, d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125630 q = 1) (hb : d163565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125630, d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40121 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15374 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125631 q = 1) (hb : d163566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125631, d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125632 q = 1) (hb : d163567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125632, d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125633 q = 1) (hb : d163568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125633, d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125634 q = 1) (hb : d163569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125634, d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125640 q = 1) (hb : d163584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125640, d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40122 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15528 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125641 q = 1) (hb : d163585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125641, d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125642 q = 1) (hb : d163586 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125642, d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125643 q = 1) (hb : d163587 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125643, d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125644 q = 1) (hb : d163588 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125644, d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125645 q = 1) (hb : d163589 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125645, d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40124 (p : Pattern) (ha : d125651 p = 1) (hb : d163595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125646 q = 1) (hb : d163590 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125646, d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40123 q ha hb
  have h2 (q : Pattern) (ha : d125647 q = 1) (hb : d163591 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125647, d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125648 q = 1) (hb : d163592 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125648, d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125649 q = 1) (hb : d163593 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125649, d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125650 q = 1) (hb : d163594 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125650, d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125651 q = 1) (hb : d163595 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125651, d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40125 (p : Pattern) (ha : d15589 p = 1) (hb : d125660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15584 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15585 q = 1) (hb : d125656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15585, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15586 q = 1) (hb : d125657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15586, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15587 q = 1) (hb : d125658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15587, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15588 q = 1) (hb : d125659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15588, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15589 q = 1) (hb : d125660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro40126 (p : Pattern) (ha : d15599 p = 1) (hb : d125665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15610 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15619 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15584 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15585 q = 1) (hb : d125656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15585, d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15705 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15586 q = 1) (hb : d125657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15586, d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15587 q = 1) (hb : d125658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15587, d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15588 q = 1) (hb : d125659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d15715 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15720 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d15594 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15595 q = 1) (hb : d125661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15595, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15596 q = 1) (hb : d125662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15596, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15597 q = 1) (hb : d125663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15597, d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15598 q = 1) (hb : d125664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15598, d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15599 q = 1) (hb : d125665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15599, d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro40127 (p : Pattern) (ha : d125672 p = 1) (hb : d163602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15595 q = 1) (hb : d125661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15595, d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15596 q = 1) (hb : d125662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15596, d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15597 q = 1) (hb : d125670 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15598 q = 1) (hb : d125671 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125672 q = 1) (hb : d163602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125672, d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro40128 (p : Pattern) (ha : d125682 p = 1) (hb : d163621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d163616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d125678 q = 1) (hb : d163617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125678, d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125679 q = 1) (hb : d163618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125679, d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d125680 q = 1) (hb : d163619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125680, d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125681 q = 1) (hb : d163620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125681, d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125682 q = 1) (hb : d163621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125682, d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40129 (p : Pattern) (ha : d125688 p = 1) (hb : d163627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d125666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40125 q ha hb
    | true =>
      simp only [d15600, d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40126 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d15601 q = 1) (hb : d125667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d125668 q = 1) (hb : d163600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125668, d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125669 q = 1) (hb : d163601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125669, d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125673 q = 1) (hb : d163603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125673, d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40127 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15762 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d125674 q = 1) (hb : d163604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125674, d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d125675 q = 1) (hb : d163605 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125675, d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d125676 q = 1) (hb : d163606 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125676, d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d125677 q = 1) (hb : d163607 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125677, d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125683 q = 1) (hb : d163622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125683, d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40128 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15906 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d125684 q = 1) (hb : d163623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125684, d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d125685 q = 1) (hb : d163624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125685, d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d125686 q = 1) (hb : d163625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125686, d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d125687 q = 1) (hb : d163626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125687, d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d125688 q = 1) (hb : d163627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125688, d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro40130 (p : Pattern) (ha : d125694 p = 1) (hb : d163633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d163628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40129 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d163629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d163630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d163631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d163632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d163633 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40131 (p : Pattern) (ha : d125700 p = 1) (hb : d163639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d163496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40100 q ha hb
    | true =>
      simp only [d125529, d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40106 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d163523 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40112 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d163524 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d163559 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40118 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d163560 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d163561 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d163596 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40124 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d163597 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d163598 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d163599 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d163634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40130 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d163635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d163636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d163637 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d163638 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d163639 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro40132 (p : Pattern) (ha : d125706 p = 1) (hb : d163645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d163640 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40131 q ha hb
    | true =>
      simp only [d125701, d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d163641 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d163642 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d163643 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d163644 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d163645 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40133 (p : Pattern) (ha : d125712 p = 1) (hb : d163651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d163646 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40132 q ha hb
    | true =>
      simp only [d125707, d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d163647 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d163648 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d163649 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d163650 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d163651 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40134 (p : Pattern) (ha : d125718 p = 1) (hb : d163657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d163652 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40133 q ha hb
    | true =>
      simp only [d125713, d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d163653 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d163654 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d163655 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d163656 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125718 q = 1) (hb : d163657 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40135 (p : Pattern) (ha : d125724 p = 1) (hb : d163663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d163658 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40134 q ha hb
    | true =>
      simp only [d125719, d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d163659 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d163660 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d163661 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d163662 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d163663 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40136 (p : Pattern) (ha : d125730 p = 1) (hb : d163669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d163664 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40135 q ha hb
    | true =>
      simp only [d125725, d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d163665 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d163666 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d163667 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d163668 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d163669 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40137 (p : Pattern) (ha : d125736 p = 1) (hb : d163675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d163670 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40136 q ha hb
    | true =>
      simp only [d125731, d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d163671 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d163672 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d163673 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d163674 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d163675 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40138 (p : Pattern) (ha : d125742 p = 1) (hb : d163681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d163676 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40137 q ha hb
    | true =>
      simp only [d125737, d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d163677 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d163678 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d163679 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d163680 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d163681 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40139 (p : Pattern) (ha : d144 p = 1) (hb : d159762 p = 1) : d159797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28 q = 1) (hb : d100904 q = 1) : d28 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d143 q = 1) (hb : d159761 q = 1) : d159796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d143, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d144 q = 1) (hb : d159762 q = 1) : d159797 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d144, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40140 (p : Pattern) (ha : d150 p = 1) (hb : d159762 p = 1) : d159803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
    | true =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d149 q = 1) (hb : d159762 q = 1) : d159802 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150 q = 1) (hb : d159762 q = 1) : d159803 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40141 (p : Pattern) (ha : d203 p = 1) (hb : d159762 p = 1) : d159816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d203 q = 1) (hb : d159762 q = 1) : d159816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d203, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40142 (p : Pattern) (ha : d4349 p = 1) (hb : d159762 p = 1) : d159827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40141 q ha hb
    | true =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h2 (q : Pattern) (ha : d4340 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4340, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d159762 q = 1) : d159819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4341, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d159762 q = 1) : d159820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d159762 q = 1) : d159821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d159762 q = 1) : d159827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d159827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d159827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40143 (p : Pattern) (ha : d231 p = 1) (hb : d159762 p = 1) : d159834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d229 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69 q = 1) (hb : d100904 q = 1) : d69 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d230 q = 1) (hb : d159761 q = 1) : d159833 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d230, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d231 q = 1) (hb : d159762 q = 1) : d159834 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d231, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40144 (p : Pattern) (ha : d237 p = 1) (hb : d159762 p = 1) : d159840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
    | true =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d236 q = 1) (hb : d159762 q = 1) : d159839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237 q = 1) (hb : d159762 q = 1) : d159840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40145 (p : Pattern) (ha : d243 p = 1) (hb : d159762 p = 1) : d159846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40144 q ha hb
    | true =>
      simp only [d238, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31408 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d240 q = 1) (hb : d159762 q = 1) : d159843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241 q = 1) (hb : d159762 q = 1) : d159844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d241, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d242 q = 1) (hb : d159762 q = 1) : d159845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d242, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d243 q = 1) (hb : d159762 q = 1) : d159846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d243, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40146 (p : Pattern) (ha : d4359 p = 1) (hb : d159762 p = 1) : d159852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40145 q ha hb
    | true =>
      simp only [d244, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
  have h2 (q : Pattern) (ha : d4355 q = 1) (hb : d159762 q = 1) : d159848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d159762 q = 1) : d159849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d159849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4356, d159849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d159762 q = 1) : d159850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d159850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d159850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d159762 q = 1) : d159851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d159851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d159851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d159762 q = 1) : d159852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d159852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d159852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40147 (p : Pattern) (ha : d156 p = 1) (hb : d159762 p = 1) : d159809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d155 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156 q = 1) (hb : d159762 q = 1) : d159809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40148 (p : Pattern) (ha : d51643 p = 1) (hb : d159762 p = 1) : d159815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40147 q ha hb
    | true =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d159762 q = 1) : d159812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d159762 q = 1) : d159813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d159762 q = 1) : d159814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51643 q = 1) (hb : d159762 q = 1) : d159815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d159815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d159815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40149 (p : Pattern) (ha : d51646 p = 1) (hb : d159762 p = 1) : d159822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40147 q ha hb
    | true =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d159762 q = 1) : d159812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, d159812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d159762 q = 1) : d159813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, d159813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d159762 q = 1) : d159814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, d159814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31421 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31422 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d204 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40141 q ha hb
    | true =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h23 (q : Pattern) (ha : d4340 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4340, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d4341 q = 1) (hb : d159762 q = 1) : d159819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d4341, d159819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51644 q = 1) (hb : d159762 q = 1) : d159820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51644, d159820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d51645 q = 1) (hb : d159762 q = 1) : d159821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51645, d159821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d51646 q = 1) (hb : d159762 q = 1) : d159822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d159822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51646, d159822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro40150 (p : Pattern) (ha : d51652 p = 1) (hb : d159762 p = 1) : d159858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31412 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31412 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31413 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d159762 q = 1) : d159823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d159823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40148 q ha hb
    | true =>
      simp only [d51647, d159823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40149 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31414 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d159762 q = 1) : d159824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d159824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d159824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d159762 q = 1) : d159825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d159825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d159825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d159762 q = 1) : d159826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d159826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d159826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d159762 q = 1) : d159828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d159828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d159828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40142 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d159762 q = 1) : d159829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d159829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, d159829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d159762 q = 1) : d159830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d159830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, d159830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d159762 q = 1) : d159831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d159831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, d159831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51651 q = 1) (hb : d159762 q = 1) : d159832 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d159832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51651, d159832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4360 q = 1) (hb : d159762 q = 1) : d159853 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d159853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d159853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40146 q ha hb
  have h17 (q : Pattern) (ha : d4361 q = 1) (hb : d159762 q = 1) : d159854 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d159854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4361, d159854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d4362 q = 1) (hb : d159762 q = 1) : d159855 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d159855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4362, d159855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4363 q = 1) (hb : d159762 q = 1) : d159856 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d159856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4363, d159856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4364 q = 1) (hb : d159762 q = 1) : d159857 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d159857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4364, d159857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51652 q = 1) (hb : d159762 q = 1) : d159858 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d159858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51652, d159858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro40151 (p : Pattern) (ha : d284 p = 1) (hb : d159762 p = 1) : d159868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40147 q ha hb
    | true =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284 q = 1) (hb : d159762 q = 1) : d159868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d159868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d159868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40152 (p : Pattern) (ha : d291 p = 1) (hb : d159762 p = 1) : d159875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40147 q ha hb
    | true =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d204 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40141 q ha hb
    | true =>
      simp only [d204, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h7 (q : Pattern) (ha : d287 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d288 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d288, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d289 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d290 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d291 q = 1) (hb : d159762 q = 1) : d159875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d291, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40153 (p : Pattern) (ha : d397 p = 1) (hb : d159762 p = 1) : d159928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40147 q ha hb
    | true =>
      simp only [d157, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31402 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d397 q = 1) (hb : d159762 q = 1) : d159928 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d159928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d397, d159928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40154 (p : Pattern) (ha : d296 p = 1) (hb : d159762 p = 1) : d159880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d296 q = 1) (hb : d159762 q = 1) : d159880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40155 (p : Pattern) (ha : d303 p = 1) (hb : d159762 p = 1) : d159887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d303 q = 1) (hb : d159762 q = 1) : d159887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40156 (p : Pattern) (ha : d4736 p = 1) (hb : d159762 p = 1) : d159809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d159762 q = 1) : d159809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40157 (p : Pattern) (ha : d15966 p = 1) (hb : d159762 p = 1) : d159892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142 q = 1) (hb : d100904 q = 1) : d142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d323 q = 1) (hb : d159761 q = 1) : d159891 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d159761, d159891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d323, d159761, d159891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12495 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15966 q = 1) (hb : d159762 q = 1) : d159892 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d159762, d159892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15966, d159762, d159892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40158 (p : Pattern) (ha : d15972 p = 1) (hb : d159762 p = 1) : d159898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40157 q ha hb
    | true =>
      simp only [d15967, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
    | true =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d159762 q = 1) : d159896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15971 q = 1) (hb : d159762 q = 1) : d159897 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15971, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15972 q = 1) (hb : d159762 q = 1) : d159898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15972, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40159 (p : Pattern) (ha : d15978 p = 1) (hb : d159762 p = 1) : d159904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40158 q ha hb
    | true =>
      simp only [d15973, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d159762 q = 1) : d159904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40160 (p : Pattern) (ha : d128195 p = 1) (hb : d159762 p = 1) : d159910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d159762 q = 1) : d159881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40154 q ha hb
    | true =>
      simp only [d297, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d159762 q = 1) : d159882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d159762 q = 1) : d159883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d159762 q = 1) : d159884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d159762 q = 1) : d159888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40155 q ha hb
    | true =>
      simp only [d304, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d159762 q = 1) : d159889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d159762 q = 1) : d159890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15979 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40159 q ha hb
    | true =>
      simp only [d15979, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40147 q ha hb
  have h9 (q : Pattern) (ha : d128191 q = 1) (hb : d159762 q = 1) : d159906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128191, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40156 q ha hb
    | true =>
      simp only [d4737, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128192 q = 1) (hb : d159762 q = 1) : d159907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128192, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128193 q = 1) (hb : d159762 q = 1) : d159908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128193, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128194 q = 1) (hb : d159762 q = 1) : d159909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128194, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128195 q = 1) (hb : d159762 q = 1) : d159910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d159910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d159910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40161 (p : Pattern) (ha : d376 p = 1) (hb : d159762 p = 1) : d159911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d154 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d154, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d295 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d376 q = 1) (hb : d159762 q = 1) : d159911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d376, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40162 (p : Pattern) (ha : d381 p = 1) (hb : d159762 p = 1) : d159916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31401 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d153 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d301 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d302 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d302, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d381 q = 1) (hb : d159762 q = 1) : d159916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d381, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40163 (p : Pattern) (ha : d5355 p = 1) (hb : d159762 p = 1) : d159816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d159762 q = 1) : d159816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40164 (p : Pattern) (ha : d15985 p = 1) (hb : d159762 p = 1) : d159920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40158 q ha hb
    | true =>
      simp only [d15973, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40140 q ha hb
    | true =>
      simp only [d151, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d159762 q = 1) : d159920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40165 (p : Pattern) (ha : d128200 p = 1) (hb : d159762 p = 1) : d159926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d159762 q = 1) : d159881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40154 q ha hb
    | true =>
      simp only [d297, d159881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31415 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d159762 q = 1) : d159882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d159882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d159762 q = 1) : d159883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d159883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d159762 q = 1) : d159884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d159884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d159762 q = 1) : d159888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40155 q ha hb
    | true =>
      simp only [d304, d159888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31416 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d159762 q = 1) : d159889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d159889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d159762 q = 1) : d159890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d159890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15979 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40159 q ha hb
    | true =>
      simp only [d15979, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40147 q ha hb
  have h9 (q : Pattern) (ha : d128191 q = 1) (hb : d159762 q = 1) : d159906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128191, d159906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d4737 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40156 q ha hb
    | true =>
      simp only [d4737, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5350 q = 1) (hb : d159762 q = 1) : d159811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5350, d159811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128192 q = 1) (hb : d159762 q = 1) : d159907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128192, d159907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128193 q = 1) (hb : d159762 q = 1) : d159908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128193, d159908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128194 q = 1) (hb : d159762 q = 1) : d159909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128194, d159909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d377 q = 1) (hb : d159762 q = 1) : d159912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d159912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40161 q ha hb
    | true =>
      simp only [d377, d159912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31421 q ha hb
  have h16 (q : Pattern) (ha : d378 q = 1) (hb : d159762 q = 1) : d159913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d159913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d159913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d379 q = 1) (hb : d159762 q = 1) : d159914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d159914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d379, d159914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d380 q = 1) (hb : d159762 q = 1) : d159915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d159915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d159915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d382 q = 1) (hb : d159762 q = 1) : d159917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d159917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40162 q ha hb
    | true =>
      simp only [d382, d159917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31422 q ha hb
  have h20 (q : Pattern) (ha : d383 q = 1) (hb : d159762 q = 1) : d159918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d159918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d159918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d384 q = 1) (hb : d159762 q = 1) : d159919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d159919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d384, d159919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15986 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40164 q ha hb
    | true =>
      simp only [d15986, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40141 q ha hb
  have h23 (q : Pattern) (ha : d128196 q = 1) (hb : d159762 q = 1) : d159922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128196, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5356 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40163 q ha hb
    | true =>
      simp only [d5356, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5357 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5357, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128197 q = 1) (hb : d159762 q = 1) : d159923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128197, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128198 q = 1) (hb : d159762 q = 1) : d159924 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d159924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128198, d159924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128199 q = 1) (hb : d159762 q = 1) : d159925 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d159925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128199, d159925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128200 q = 1) (hb : d159762 q = 1) : d159926 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d159926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128200, d159926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro40166 (p : Pattern) (ha : d128207 p = 1) (hb : d159762 p = 1) : d159935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40164 q ha hb
    | true =>
      simp only [d15986, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40141 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d159762 q = 1) : d159922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d159922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40163 q ha hb
    | true =>
      simp only [d5356, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d159762 q = 1) : d159818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d159818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d159762 q = 1) : d159923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d159923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d159762 q = 1) : d159933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d159933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d159933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d159762 q = 1) : d159934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d159934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d159934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d159762 q = 1) : d159935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d159935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d159935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40167 (p : Pattern) (ha : d5377 p = 1) (hb : d159762 p = 1) : d159846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40144 q ha hb
    | true =>
      simp only [d238, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d159762 q = 1) : d159843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d159762 q = 1) : d159844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d159762 q = 1) : d159845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d159762 q = 1) : d159846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40168 (p : Pattern) (ha : d16004 p = 1) (hb : d159762 p = 1) : d159942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d229 q = 1) (hb : d100904 q = 1) : d229 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d416 q = 1) (hb : d159761 q = 1) : d159941 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d159761, d159941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d416, d159761, d159941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12603 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16004 q = 1) (hb : d159762 q = 1) : d159942 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d159762, d159942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16004, d159762, d159942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40169 (p : Pattern) (ha : d16010 p = 1) (hb : d159762 p = 1) : d159948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40168 q ha hb
    | true =>
      simp only [d16005, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
    | true =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d159762 q = 1) : d159946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16009 q = 1) (hb : d159762 q = 1) : d159947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16009, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16010 q = 1) (hb : d159762 q = 1) : d159948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16010, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro40170 (p : Pattern) (ha : d16016 p = 1) (hb : d159762 p = 1) : d159954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40169 q ha hb
    | true =>
      simp only [d16011, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40144 q ha hb
    | true =>
      simp only [d238, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d159762 q = 1) : d159951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d159762 q = 1) : d159952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d159762 q = 1) : d159953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d159762 q = 1) : d159954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40171 (p : Pattern) (ha : d128217 p = 1) (hb : d159762 p = 1) : d159960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d159762 q = 1) : d159955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40170 q ha hb
    | true =>
      simp only [d16017, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40145 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d159762 q = 1) : d159956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d159956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d159956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40167 q ha hb
    | true =>
      simp only [d5378, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d159762 q = 1) : d159848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d159848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d159762 q = 1) : d159957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d159957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d159957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d159762 q = 1) : d159958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d159958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d159958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d159762 q = 1) : d159959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d159959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d159959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d159762 q = 1) : d159960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d159960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d159960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40172 (p : Pattern) (ha : d128223 p = 1) (hb : d159762 p = 1) : d159966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d159762 q = 1) : d159869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d159869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d159869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40151 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d159762 q = 1) : d159870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d159870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d159870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d159762 q = 1) : d159876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40151 q ha hb
    | true =>
      simp only [d292, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40152 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d159762 q = 1) : d159877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d159762 q = 1) : d159878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d159878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d159878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d159762 q = 1) : d159927 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d159927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40160 q ha hb
    | true =>
      simp only [d128201, d159927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40165 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d159762 q = 1) : d159929 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d159929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40153 q ha hb
    | true =>
      simp only [d398, d159929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31413 q ha hb
  have h8 (q : Pattern) (ha : d128202 q = 1) (hb : d159762 q = 1) : d159930 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d159930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d159930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128203 q = 1) (hb : d159762 q = 1) : d159931 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d159931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128203, d159931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128204 q = 1) (hb : d159762 q = 1) : d159932 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d159932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d159932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128208 q = 1) (hb : d159762 q = 1) : d159936 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d159936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d159936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40166 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31431 q ha hb
  have h13 (q : Pattern) (ha : d128209 q = 1) (hb : d159762 q = 1) : d159937 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d159937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128209, d159937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128210 q = 1) (hb : d159762 q = 1) : d159938 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d159938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128210, d159938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128211 q = 1) (hb : d159762 q = 1) : d159939 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d159939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128211, d159939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128212 q = 1) (hb : d159762 q = 1) : d159940 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d159940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128212, d159940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128218 q = 1) (hb : d159762 q = 1) : d159961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d159961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d159961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40171 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31432 q ha hb
  have h19 (q : Pattern) (ha : d128219 q = 1) (hb : d159762 q = 1) : d159962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d159962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128219, d159962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128220 q = 1) (hb : d159762 q = 1) : d159963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d159963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128220, d159963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128221 q = 1) (hb : d159762 q = 1) : d159964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d159964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128221, d159964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128222 q = 1) (hb : d159762 q = 1) : d159965 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d159965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128222, d159965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128223 q = 1) (hb : d159762 q = 1) : d159966 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d159966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128223, d159966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40173 (p : Pattern) (ha : d128229 p = 1) (hb : d159762 p = 1) : d159972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31411 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d159762 q = 1) : d159859 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d159859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d159859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40150 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d159762 q = 1) : d159860 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d159860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d159860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d159762 q = 1) : d159861 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d159861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d159861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d159762 q = 1) : d159862 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d159862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d159862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d159762 q = 1) : d159863 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d159863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d159863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128224 q = 1) (hb : d159762 q = 1) : d159967 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d159967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128224, d159967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40172 q ha hb
  have h11 (q : Pattern) (ha : d128225 q = 1) (hb : d159762 q = 1) : d159968 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d159968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128225, d159968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128226 q = 1) (hb : d159762 q = 1) : d159969 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d159969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128226, d159969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128227 q = 1) (hb : d159762 q = 1) : d159970 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d159970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128227, d159970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128228 q = 1) (hb : d159762 q = 1) : d159971 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d159971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128228, d159971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128229 q = 1) (hb : d159762 q = 1) : d159972 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d159972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128229, d159972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40174 (p : Pattern) (ha : d481 p = 1) (hb : d159762 p = 1) : d159803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
    | true =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d480 q = 1) (hb : d159762 q = 1) : d159802 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d480, d159802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d481 q = 1) (hb : d159762 q = 1) : d159803 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d481, d159803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40175 (p : Pattern) (ha : d491 p = 1) (hb : d159762 p = 1) : d159809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d159762 q = 1) : d159809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d159809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40176 (p : Pattern) (ha : d501 p = 1) (hb : d159762 p = 1) : d159816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d159762 q = 1) : d159808 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d159808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d159762 q = 1) : d159816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d159816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40177 (p : Pattern) (ha : d644 p = 1) (hb : d159762 p = 1) : d159875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40175 q ha hb
    | true =>
      simp only [d633, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40176 q ha hb
    | true =>
      simp only [d639, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d159762 q = 1) : d159875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d159875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40178 (p : Pattern) (ha : d653 p = 1) (hb : d159762 p = 1) : d160055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40176 q ha hb
    | true =>
      simp only [d639, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d159762 q = 1) : d160055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40179 (p : Pattern) (ha : d683 p = 1) (hb : d159762 p = 1) : d159840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
    | true =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d682 q = 1) (hb : d159762 q = 1) : d159839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, d159839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d683 q = 1) (hb : d159762 q = 1) : d159840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d683, d159840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40180 (p : Pattern) (ha : d730 p = 1) (hb : d159762 p = 1) : d159846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40179 q ha hb
    | true =>
      simp only [d684, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d159762 q = 1) : d159843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d159843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d159762 q = 1) : d159844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d159844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d159762 q = 1) : d159845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d159845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d159762 q = 1) : d159846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d159846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40181 (p : Pattern) (ha : d736 p = 1) (hb : d159762 p = 1) : d160092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40180 q ha hb
    | true =>
      simp only [d731, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d159762 q = 1) : d160088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d159762 q = 1) : d160089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d159762 q = 1) : d160090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d159762 q = 1) : d160091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d159762 q = 1) : d160092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40182 (p : Pattern) (ha : d16036 p = 1) (hb : d159762 p = 1) : d159898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40157 q ha hb
    | true =>
      simp only [d15967, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
    | true =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d159762 q = 1) : d159896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d475 q = 1) (hb : d159762 q = 1) : d159801 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d475, d159801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16035 q = 1) (hb : d159762 q = 1) : d159897 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16035, d159897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16036 q = 1) (hb : d159762 q = 1) : d159898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16036, d159898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40183 (p : Pattern) (ha : d16042 p = 1) (hb : d159762 p = 1) : d159904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d159762 q = 1) : d159904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d159904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40184 (p : Pattern) (ha : d16048 p = 1) (hb : d159762 p = 1) : d159977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40183 q ha hb
    | true =>
      simp only [d16043, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40175 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d159762 q = 1) : d159973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d159762 q = 1) : d159974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d159762 q = 1) : d159975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d159762 q = 1) : d159976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d159762 q = 1) : d159977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d159977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d159977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40185 (p : Pattern) (ha : d16051 p = 1) (hb : d159762 p = 1) : d159920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d159762 q = 1) : d159903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d159903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d159762 q = 1) : d159920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d159920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40186 (p : Pattern) (ha : d16057 p = 1) (hb : d159762 p = 1) : d159984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40183 q ha hb
    | true =>
      simp only [d16043, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40175 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d159762 q = 1) : d159973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d159762 q = 1) : d159974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d159762 q = 1) : d159975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d159762 q = 1) : d159976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40185 q ha hb
    | true =>
      simp only [d16052, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40176 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d159762 q = 1) : d159980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d159762 q = 1) : d159981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d159762 q = 1) : d159982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d159762 q = 1) : d159983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d159762 q = 1) : d159984 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d159984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d159984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40187 (p : Pattern) (ha : d16143 p = 1) (hb : d159762 p = 1) : d160046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d159762 q = 1) : d159905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40183 q ha hb
    | true =>
      simp only [d16043, d159905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40175 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d159762 q = 1) : d159973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d159973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d159762 q = 1) : d159974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d159974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d159762 q = 1) : d159975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d159975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d159762 q = 1) : d159976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d159976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d159762 q = 1) : d159810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40175 q ha hb
    | true =>
      simp only [d633, d159810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d159762 q = 1) : d159864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d159864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d159762 q = 1) : d159865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d159865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d159762 q = 1) : d159866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d159866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d159762 q = 1) : d159867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d159867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d159762 q = 1) : d160046 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d160046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d160046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40188 (p : Pattern) (ha : d514 p = 1) (hb : d159762 p = 1) : d159880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d159762 q = 1) : d159880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d159880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40189 (p : Pattern) (ha : d524 p = 1) (hb : d159762 p = 1) : d159887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d159762 q = 1) : d159887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d159887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40190 (p : Pattern) (ha : d16062 p = 1) (hb : d159762 p = 1) : d159989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d159762 q = 1) : d159988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d159762 q = 1) : d159989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d159989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d159989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40191 (p : Pattern) (ha : d16069 p = 1) (hb : d159762 p = 1) : d159996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d159762 q = 1) : d159994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d159762 q = 1) : d159995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d159762 q = 1) : d159996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d159996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d159996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40192 (p : Pattern) (ha : d16077 p = 1) (hb : d159762 p = 1) : d178226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16074 q = 1) (hb : d100904 q = 1) : d16074 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16075 q = 1) (hb : d159761 q = 1) : d178225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d159761, d178225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16075, d159761, d178225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16076 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16077 q = 1) (hb : d159762 q = 1) : d178226 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d159762, d178226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16077, d159762, d178226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40193 (p : Pattern) (ha : d16081 p = 1) (hb : d159762 p = 1) : d159797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12494 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28 q = 1) (hb : d100904 q = 1) : d28 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12495 q = 1) (hb : d159761 q = 1) : d159796 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12495, d159761, d159796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16081 q = 1) (hb : d159762 q = 1) : d159797 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16081, d159762, d159797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40194 (p : Pattern) (ha : d16087 p = 1) (hb : d159762 p = 1) : d178232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d159762 q = 1) : d178227 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d178227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40192 q ha hb
    | true =>
      simp only [d16078, d178227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40157 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d159762 q = 1) : d178228 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d178228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d178228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d159762 q = 1) : d178229 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d178229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d178229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40157 q ha hb
    | true =>
      simp only [d16082, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40193 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d159762 q = 1) : d178230 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d178230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d178230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d159762 q = 1) : d159893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40157 q ha hb
    | true =>
      simp only [d15967, d159893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d159762 q = 1) : d159894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d159894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d159762 q = 1) : d159895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d159895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145 q = 1) (hb : d159762 q = 1) : d159798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40139 q ha hb
    | true =>
      simp only [d145, d159798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31400 q ha hb
  have h12 (q : Pattern) (ha : d146 q = 1) (hb : d159762 q = 1) : d159799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d159799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147 q = 1) (hb : d159762 q = 1) : d159800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d159800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15970 q = 1) (hb : d159762 q = 1) : d159896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d159896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16086 q = 1) (hb : d159762 q = 1) : d178231 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d178231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d178231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16087 q = 1) (hb : d159762 q = 1) : d178232 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d178232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16087, d178232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40195 (p : Pattern) (ha : d16093 p = 1) (hb : d159762 p = 1) : d178238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d159762 q = 1) : d178233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d178233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40194 q ha hb
    | true =>
      simp only [d16088, d178233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d159762 q = 1) : d178234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d178234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d178234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d159762 q = 1) : d178235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d178235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d178235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d159762 q = 1) : d178236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d178236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d178236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d159762 q = 1) : d178237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d178237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d178237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d159762 q = 1) : d178238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d178238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d178238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40196 (p : Pattern) (ha : d16114 p = 1) (hb : d159762 p = 1) : d160019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d159762 q = 1) : d160016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d159762 q = 1) : d160017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d159762 q = 1) : d160018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d159762 q = 1) : d160019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d160019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d160019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40197 (p : Pattern) (ha : d128234 p = 1) (hb : d159762 p = 1) : d178244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d159762 q = 1) : d159990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40190 q ha hb
    | true =>
      simp only [d16063, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40188 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d159762 q = 1) : d159991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d159762 q = 1) : d159992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d159762 q = 1) : d159993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d159762 q = 1) : d159997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40191 q ha hb
    | true =>
      simp only [d16070, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40189 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d159762 q = 1) : d159998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d159762 q = 1) : d159999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d159762 q = 1) : d178239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d178239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40195 q ha hb
    | true =>
      simp only [d16094, d178239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40183 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d159762 q = 1) : d178240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d178240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d178240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d159762 q = 1) : d160020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40196 q ha hb
    | true =>
      simp only [d16115, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d159762 q = 1) : d160021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d159762 q = 1) : d178241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d178241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d178241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d159762 q = 1) : d178242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d178242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d178242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d159762 q = 1) : d178243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d178243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d178243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128234 q = 1) (hb : d159762 q = 1) : d178244 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d178244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d178244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40198 (p : Pattern) (ha : d610 p = 1) (hb : d159762 p = 1) : d159911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d159762 q = 1) : d159807 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d159807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d159762 q = 1) : d159879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d159879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d159762 q = 1) : d159911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d159911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40199 (p : Pattern) (ha : d616 p = 1) (hb : d159762 p = 1) : d159916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d159762 q = 1) : d159806 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d159806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d159762 q = 1) : d159885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d159885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d159762 q = 1) : d159886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d159886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d159762 q = 1) : d159916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d159916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40200 (p : Pattern) (ha : d16121 p = 1) (hb : d159762 p = 1) : d160026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d159762 q = 1) : d159902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d159902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d159762 q = 1) : d159988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d159988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d159762 q = 1) : d160026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d160026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d160026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40201 (p : Pattern) (ha : d16126 p = 1) (hb : d159762 p = 1) : d160031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d159762 q = 1) : d159804 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40174 q ha hb
    | true =>
      simp only [d482, d159804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d159762 q = 1) : d159805 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d159805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d159762 q = 1) : d159901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d159901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d159762 q = 1) : d159994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d159994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d159762 q = 1) : d159995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d159995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d159762 q = 1) : d160031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d160031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d160031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40202 (p : Pattern) (ha : d16130 p = 1) (hb : d159762 p = 1) : d178245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d159762 q = 1) : d178233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d178233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40194 q ha hb
    | true =>
      simp only [d16088, d178233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d159762 q = 1) : d178234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d178234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d178234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d159762 q = 1) : d178235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d178235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d178235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d159762 q = 1) : d178236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d178236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d178236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d159762 q = 1) : d178237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d178237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d178237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d159762 q = 1) : d178245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d178245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d178245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40203 (p : Pattern) (ha : d16135 p = 1) (hb : d159762 p = 1) : d160038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d159762 q = 1) : d159899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40182 q ha hb
    | true =>
      simp only [d16037, d159899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d159762 q = 1) : d159900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d159900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d159762 q = 1) : d160016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d160016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d159762 q = 1) : d160017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d160017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d159762 q = 1) : d160018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d160018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d159762 q = 1) : d160038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d160038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d160038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40204 (p : Pattern) (ha : d128239 p = 1) (hb : d159762 p = 1) : d178251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d159762 q = 1) : d159990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40190 q ha hb
    | true =>
      simp only [d16063, d159990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40188 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d159762 q = 1) : d159991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d159991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d159762 q = 1) : d159992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d159992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d159762 q = 1) : d159993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d159993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d159762 q = 1) : d159997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40191 q ha hb
    | true =>
      simp only [d16070, d159997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40189 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d159762 q = 1) : d159998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d159998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d159762 q = 1) : d159999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d159999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d159762 q = 1) : d178239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d178239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40195 q ha hb
    | true =>
      simp only [d16094, d178239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40183 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d159762 q = 1) : d178240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d178240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d178240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d159762 q = 1) : d160020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40196 q ha hb
    | true =>
      simp only [d16115, d160020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d159762 q = 1) : d160021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d160021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d159762 q = 1) : d178241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d178241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d178241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d159762 q = 1) : d178242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d178242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d178242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d159762 q = 1) : d178243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d178243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d178243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d159762 q = 1) : d160027 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d160027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40200 q ha hb
    | true =>
      simp only [d16122, d160027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40198 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d159762 q = 1) : d160028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d160028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d160028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d159762 q = 1) : d160029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d160029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d160029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d159762 q = 1) : d160030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d160030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d160030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d159762 q = 1) : d160032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d160032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40201 q ha hb
    | true =>
      simp only [d16127, d160032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40199 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d159762 q = 1) : d160033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d160033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d160033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d159762 q = 1) : d160034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d160034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d160034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d159762 q = 1) : d178246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d178246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40202 q ha hb
    | true =>
      simp only [d16131, d178246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40185 q ha hb
  have h23 (q : Pattern) (ha : d128235 q = 1) (hb : d159762 q = 1) : d178247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d178247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128235, d178247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d159762 q = 1) : d160039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40203 q ha hb
    | true =>
      simp only [d16136, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d159762 q = 1) : d160040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128236 q = 1) (hb : d159762 q = 1) : d178248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d178248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d178248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128237 q = 1) (hb : d159762 q = 1) : d178249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d178249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128237, d178249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128238 q = 1) (hb : d159762 q = 1) : d178250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d178250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128238, d178250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128239 q = 1) (hb : d159762 q = 1) : d178251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d178251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d178251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro40205 (p : Pattern) (ha : d128246 p = 1) (hb : d159762 p = 1) : d178258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d159762 q = 1) : d178246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d178246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40202 q ha hb
    | true =>
      simp only [d16131, d178246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40185 q ha hb
  have h2 (q : Pattern) (ha : d128235 q = 1) (hb : d159762 q = 1) : d178247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d178247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d178247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d159762 q = 1) : d160039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40203 q ha hb
    | true =>
      simp only [d16136, d160039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d159762 q = 1) : d160040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d160040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d159762 q = 1) : d178248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d178248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d178248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d159762 q = 1) : d178256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d178256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d178256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d159762 q = 1) : d178257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d178257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d178257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d159762 q = 1) : d178258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d178258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d178258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40206 (p : Pattern) (ha : d16162 p = 1) (hb : d159762 p = 1) : d178265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16159 q = 1) (hb : d100904 q = 1) : d16159 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16160 q = 1) (hb : d159761 q = 1) : d178264 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d159761, d178264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16160, d159761, d178264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16161 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16162 q = 1) (hb : d159762 q = 1) : d178265 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d159762, d178265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16162, d159762, d178265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40207 (p : Pattern) (ha : d16166 p = 1) (hb : d159762 p = 1) : d159834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12602 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69 q = 1) (hb : d100904 q = 1) : d69 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12603 q = 1) (hb : d159761 q = 1) : d159833 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12603, d159761, d159833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16166 q = 1) (hb : d159762 q = 1) : d159834 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16166, d159762, d159834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40208 (p : Pattern) (ha : d16172 p = 1) (hb : d159762 p = 1) : d178271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d159762 q = 1) : d178266 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d178266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40206 q ha hb
    | true =>
      simp only [d16163, d178266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40168 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d159762 q = 1) : d178267 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d178267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d178267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d159762 q = 1) : d178268 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d178268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d178268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40168 q ha hb
    | true =>
      simp only [d16167, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40207 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d159762 q = 1) : d178269 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d178269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d178269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40168 q ha hb
    | true =>
      simp only [d16005, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d232 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
    | true =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h12 (q : Pattern) (ha : d233 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16008 q = 1) (hb : d159762 q = 1) : d159946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16171 q = 1) (hb : d159762 q = 1) : d178270 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d178270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d178270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16172 q = 1) (hb : d159762 q = 1) : d178271 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d178271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16172, d178271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40209 (p : Pattern) (ha : d16176 p = 1) (hb : d159762 p = 1) : d159948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d159762 q = 1) : d159943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40168 q ha hb
    | true =>
      simp only [d16005, d159943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d159762 q = 1) : d159944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d159944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d159762 q = 1) : d159945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d159945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d159762 q = 1) : d159835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40143 q ha hb
    | true =>
      simp only [d232, d159835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31407 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d159762 q = 1) : d159836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d159836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d159762 q = 1) : d159837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d159837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d159762 q = 1) : d159946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d159946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d673 q = 1) (hb : d159762 q = 1) : d159838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d673, d159838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16175 q = 1) (hb : d159762 q = 1) : d159947 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16175, d159947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16176 q = 1) (hb : d159762 q = 1) : d159948 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16176, d159948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40210 (p : Pattern) (ha : d16182 p = 1) (hb : d159762 p = 1) : d178277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d159762 q = 1) : d178272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d178272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40208 q ha hb
    | true =>
      simp only [d16173, d178272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d159762 q = 1) : d178273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d178273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d178273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40209 q ha hb
    | true =>
      simp only [d16177, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d159762 q = 1) : d178274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d178274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d178274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d159762 q = 1) : d178275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d178275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d178275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d159762 q = 1) : d178276 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d178276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d178276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d159762 q = 1) : d178277 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d178277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d178277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40211 (p : Pattern) (ha : d16186 p = 1) (hb : d159762 p = 1) : d159954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40209 q ha hb
    | true =>
      simp only [d16177, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d159762 q = 1) : d159841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40179 q ha hb
    | true =>
      simp only [d684, d159841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d159762 q = 1) : d159842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d159842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d159762 q = 1) : d159951 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d159951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d159762 q = 1) : d159952 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d159952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d159762 q = 1) : d159953 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d159953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d159762 q = 1) : d159954 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d159954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40212 (p : Pattern) (ha : d16207 p = 1) (hb : d159762 p = 1) : d160080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d159762 q = 1) : d159949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40209 q ha hb
    | true =>
      simp only [d16177, d159949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d159762 q = 1) : d159950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d159950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d159762 q = 1) : d160077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d160077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d160077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d159762 q = 1) : d160078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d160078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d160078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d159762 q = 1) : d160079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d160079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d160079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d159762 q = 1) : d160080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d160080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d160080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40213 (p : Pattern) (ha : d128256 p = 1) (hb : d159762 p = 1) : d178283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d159762 q = 1) : d178278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d178278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40210 q ha hb
    | true =>
      simp only [d16187, d178278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40211 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d159762 q = 1) : d178279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d178279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d178279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d159762 q = 1) : d160081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d160081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40212 q ha hb
    | true =>
      simp only [d16208, d160081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d159762 q = 1) : d160082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d160082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d160082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d159762 q = 1) : d178280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d178280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d178280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d159762 q = 1) : d178281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d178281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d178281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d159762 q = 1) : d178282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d178282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d178282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d159762 q = 1) : d178283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d178283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d178283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40214 (p : Pattern) (ha : d128262 p = 1) (hb : d159762 p = 1) : d178289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d159762 q = 1) : d159978 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d159978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d159978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40184 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d159762 q = 1) : d159979 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d159979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d159979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d159762 q = 1) : d159985 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40184 q ha hb
    | true =>
      simp only [d16058, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40186 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d159762 q = 1) : d159986 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d159762 q = 1) : d159987 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d159987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d159987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128240 q = 1) (hb : d159762 q = 1) : d178252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d178252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40197 q ha hb
    | true =>
      simp only [d128240, d178252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40204 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d159762 q = 1) : d160047 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d160047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40187 q ha hb
    | true =>
      simp only [d16144, d160047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40177 q ha hb
  have h8 (q : Pattern) (ha : d128241 q = 1) (hb : d159762 q = 1) : d178253 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d178253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d178253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128242 q = 1) (hb : d159762 q = 1) : d178254 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d178254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d178254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128243 q = 1) (hb : d159762 q = 1) : d178255 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d178255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128243, d178255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128247 q = 1) (hb : d159762 q = 1) : d178259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d178259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128247, d178259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40205 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d159762 q = 1) : d160056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40178 q ha hb
  have h13 (q : Pattern) (ha : d128248 q = 1) (hb : d159762 q = 1) : d178260 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d178260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d178260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128249 q = 1) (hb : d159762 q = 1) : d178261 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d178261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d178261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128250 q = 1) (hb : d159762 q = 1) : d178262 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d178262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d178262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128251 q = 1) (hb : d159762 q = 1) : d178263 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d178263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d178263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128257 q = 1) (hb : d159762 q = 1) : d178284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d178284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128257, d178284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40213 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d159762 q = 1) : d160093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40181 q ha hb
  have h19 (q : Pattern) (ha : d128258 q = 1) (hb : d159762 q = 1) : d178285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d178285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d178285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128259 q = 1) (hb : d159762 q = 1) : d178286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d178286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d178286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128260 q = 1) (hb : d159762 q = 1) : d178287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d178287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d178287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128261 q = 1) (hb : d159762 q = 1) : d178288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d178288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d178288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128262 q = 1) (hb : d159762 q = 1) : d178289 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d178289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d178289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro40215 (p : Pattern) (ha : d128268 p = 1) (hb : d159762 p = 1) : d178295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d159762 q = 1) : d178290 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d178290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d178290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40214 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d159762 q = 1) : d178291 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d178291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d178291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d159762 q = 1) : d178292 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d178292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d178292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d159762 q = 1) : d178293 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d178293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d178293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d159762 q = 1) : d178294 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d178294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d178294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d159762 q = 1) : d178295 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d178295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d178295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40216 (p : Pattern) (ha : d758 p = 1) (hb : d159762 p = 1) : d160107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d754 q = 1) (hb : d100904 q = 1) : d754 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d755 q = 1) (hb : d159761 q = 1) : d160106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d755, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d758 q = 1) (hb : d159762 q = 1) : d160107 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d758, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40217 (p : Pattern) (ha : d773 p = 1) (hb : d159762 p = 1) : d160121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d159762 q = 1) : d160111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40216 q ha hb
    | true =>
      simp only [d763, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31498 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d159762 q = 1) : d160112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d159762 q = 1) : d160113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d159762 q = 1) : d160115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d159762 q = 1) : d160120 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d160120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d160120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d159762 q = 1) : d160121 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d160121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d160121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40218 (p : Pattern) (ha : d783 p = 1) (hb : d159762 p = 1) : d160131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d159762 q = 1) : d160130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d159762 q = 1) : d160131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d160131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d160131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40219 (p : Pattern) (ha : d793 p = 1) (hb : d159762 p = 1) : d160141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d159762 q = 1) : d160130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d159762 q = 1) : d160141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d160141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d160141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40220 (p : Pattern) (ha : d950 p = 1) (hb : d159762 p = 1) : d160227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d159762 q = 1) : d160216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40218 q ha hb
    | true =>
      simp only [d939, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d159762 q = 1) : d160217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d159762 q = 1) : d160218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d159762 q = 1) : d160219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d159762 q = 1) : d160220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d159762 q = 1) : d160222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40219 q ha hb
    | true =>
      simp only [d945, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d159762 q = 1) : d160223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d159762 q = 1) : d160224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d159762 q = 1) : d160225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d159762 q = 1) : d160226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d159762 q = 1) : d160227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d160227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d160227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40221 (p : Pattern) (ha : d959 p = 1) (hb : d159762 p = 1) : d160236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d159762 q = 1) : d160222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40219 q ha hb
    | true =>
      simp only [d945, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d159762 q = 1) : d160223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d159762 q = 1) : d160224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d159762 q = 1) : d160225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d159762 q = 1) : d160226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d159762 q = 1) : d160236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d160236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d160236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40222 (p : Pattern) (ha : d981 p = 1) (hb : d159762 p = 1) : d160248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d974 q = 1) (hb : d100904 q = 1) : d974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d975 q = 1) (hb : d159761 q = 1) : d160247 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d975, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d981 q = 1) (hb : d159762 q = 1) : d160248 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d981, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40223 (p : Pattern) (ha : d1005 p = 1) (hb : d159762 p = 1) : d160271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d159762 q = 1) : d160253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40222 q ha hb
    | true =>
      simp only [d987, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31511 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d159762 q = 1) : d160254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d159762 q = 1) : d160255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d159762 q = 1) : d160261 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d159762 q = 1) : d160270 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d160270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d160270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d159762 q = 1) : d160271 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d160271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d160271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40224 (p : Pattern) (ha : d1063 p = 1) (hb : d159762 p = 1) : d160294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d159762 q = 1) : d160272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40223 q ha hb
    | true =>
      simp only [d1006, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d159762 q = 1) : d160273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d159762 q = 1) : d160291 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d160291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d160291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d159762 q = 1) : d160292 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d160292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d160292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d159762 q = 1) : d160293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d160293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d160293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d159762 q = 1) : d160294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d160294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d160294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40225 (p : Pattern) (ha : d1069 p = 1) (hb : d159762 p = 1) : d160300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d159762 q = 1) : d160295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d160295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40224 q ha hb
    | true =>
      simp only [d1064, d160295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d159762 q = 1) : d160296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d160296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d160296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d159762 q = 1) : d160297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d160297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d160297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d159762 q = 1) : d160298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d160298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d160298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d159762 q = 1) : d160299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d160299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d160299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d159762 q = 1) : d160300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d160300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d160300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40226 (p : Pattern) (ha : d16227 p = 1) (hb : d159762 p = 1) : d178226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d546 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16074 q = 1) (hb : d100904 q = 1) : d16074 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16075 q = 1) (hb : d159761 q = 1) : d178225 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d159761, d178225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16075, d159761, d178225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12750 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16227 q = 1) (hb : d159762 q = 1) : d178226 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d159762, d178226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16227, d159762, d178226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40227 (p : Pattern) (ha : d16233 p = 1) (hb : d159762 p = 1) : d178302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d159762 q = 1) : d178297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d178297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40226 q ha hb
    | true =>
      simp only [d16228, d178297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40216 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d159762 q = 1) : d178298 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d178298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d178298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d159762 q = 1) : d178299 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d178299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d178299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d159762 q = 1) : d160111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40216 q ha hb
    | true =>
      simp only [d763, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31498 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d159762 q = 1) : d160112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d159762 q = 1) : d160113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16231 q = 1) (hb : d159762 q = 1) : d178300 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d178300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d178300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d159762 q = 1) : d160115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16232 q = 1) (hb : d159762 q = 1) : d178301 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d178301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16232, d178301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16233 q = 1) (hb : d159762 q = 1) : d178302 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d178302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16233, d178302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro40228 (p : Pattern) (ha : d16239 p = 1) (hb : d159762 p = 1) : d178308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d159762 q = 1) : d178305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d159762 q = 1) : d178306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d159762 q = 1) : d178307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d178307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d178307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d159762 q = 1) : d178308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d178308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d178308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40229 (p : Pattern) (ha : d16245 p = 1) (hb : d159762 p = 1) : d178314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d159762 q = 1) : d178309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d178309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40228 q ha hb
    | true =>
      simp only [d16240, d178309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40218 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d159762 q = 1) : d178310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d178310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d178310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d159762 q = 1) : d178311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d178311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d178311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d159762 q = 1) : d178312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d178312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d178312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d159762 q = 1) : d178313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d178313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d178313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d159762 q = 1) : d178314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d178314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d178314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40230 (p : Pattern) (ha : d16248 p = 1) (hb : d159762 p = 1) : d178317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d159762 q = 1) : d178305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d159762 q = 1) : d178306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d159762 q = 1) : d178307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d178307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d178307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d159762 q = 1) : d178317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d178317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d178317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40231 (p : Pattern) (ha : d16254 p = 1) (hb : d159762 p = 1) : d178323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d159762 q = 1) : d178309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d178309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40228 q ha hb
    | true =>
      simp only [d16240, d178309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40218 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d159762 q = 1) : d178310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d178310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d178310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d159762 q = 1) : d178311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d178311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d178311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d159762 q = 1) : d178312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d178312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d178312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d159762 q = 1) : d178313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d178313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d178313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d159762 q = 1) : d178318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d178318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40230 q ha hb
    | true =>
      simp only [d16249, d178318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40219 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d159762 q = 1) : d178319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d178319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d178319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d159762 q = 1) : d178320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d178320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d178320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d159762 q = 1) : d178321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d178321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d178321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d159762 q = 1) : d178322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d178322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d178322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d159762 q = 1) : d178323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d178323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d178323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40232 (p : Pattern) (ha : d16343 p = 1) (hb : d159762 p = 1) : d178385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d159762 q = 1) : d178309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d178309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40228 q ha hb
    | true =>
      simp only [d16240, d178309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40218 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d159762 q = 1) : d178310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d178310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d178310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d159762 q = 1) : d178311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d178311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d178311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d159762 q = 1) : d178312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d178312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d178312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d159762 q = 1) : d178313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d178313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d178313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d159762 q = 1) : d160216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40218 q ha hb
    | true =>
      simp only [d939, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d159762 q = 1) : d160217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d159762 q = 1) : d160218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d159762 q = 1) : d160219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d159762 q = 1) : d160220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d159762 q = 1) : d178385 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d178385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d178385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro40233 (p : Pattern) (ha : d806 p = 1) (hb : d159762 p = 1) : d160154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d159762 q = 1) : d160153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d159762 q = 1) : d160154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d160154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d160154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40234 (p : Pattern) (ha : d816 p = 1) (hb : d159762 p = 1) : d160164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d159762 q = 1) : d160162 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d159762 q = 1) : d160163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d159762 q = 1) : d160164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d160164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d160164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40235 (p : Pattern) (ha : d16259 p = 1) (hb : d159762 p = 1) : d178328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d159762 q = 1) : d178305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d159762 q = 1) : d178306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d159762 q = 1) : d178327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d178327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d178327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d159762 q = 1) : d178328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d178328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d178328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40236 (p : Pattern) (ha : d16266 p = 1) (hb : d159762 p = 1) : d178335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d159762 q = 1) : d178305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d159762 q = 1) : d178333 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d178333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d178333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d159762 q = 1) : d178334 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d178334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d178334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d159762 q = 1) : d178335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d178335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d178335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40237 (p : Pattern) (ha : d16274 p = 1) (hb : d159762 p = 1) : d178340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16271 q = 1) (hb : d100904 q = 1) : d16271 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d16272 q = 1) (hb : d159761 q = 1) : d178339 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d159761, d178339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d16272, d159761, d178339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16273 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16274 q = 1) (hb : d159762 q = 1) : d178340 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d159762, d178340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16274, d159762, d178340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40238 (p : Pattern) (ha : d16278 p = 1) (hb : d159762 p = 1) : d160107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d754 q = 1) (hb : d100904 q = 1) : d754 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12750 q = 1) (hb : d159761 q = 1) : d160106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12750, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d16278 q = 1) (hb : d159762 q = 1) : d160107 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16278, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro40239 (p : Pattern) (ha : d16284 p = 1) (hb : d159762 p = 1) : d178346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d159762 q = 1) : d178341 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d178341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40237 q ha hb
    | true =>
      simp only [d16275, d178341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40226 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d159762 q = 1) : d178342 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d178342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d178342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d159762 q = 1) : d178343 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d178343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d178343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d159762 q = 1) : d178297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d178297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40226 q ha hb
    | true =>
      simp only [d16279, d178297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40238 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d159762 q = 1) : d178298 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d178298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d178298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d159762 q = 1) : d178299 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d178299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d178299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d159762 q = 1) : d178344 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d178344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d178344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d159762 q = 1) : d178297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d178297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40226 q ha hb
    | true =>
      simp only [d16228, d178297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40216 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d159762 q = 1) : d178298 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d178298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d178298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d159762 q = 1) : d178299 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d178299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d178299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d159762 q = 1) : d160111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40216 q ha hb
    | true =>
      simp only [d763, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31498 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d159762 q = 1) : d160112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d159762 q = 1) : d160113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16231 q = 1) (hb : d159762 q = 1) : d178300 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d178300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d178300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16283 q = 1) (hb : d159762 q = 1) : d178345 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d178345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d178345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16284 q = 1) (hb : d159762 q = 1) : d178346 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d178346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16284, d178346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro40240 (p : Pattern) (ha : d16290 p = 1) (hb : d159762 p = 1) : d178352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d159762 q = 1) : d178347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d178347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40239 q ha hb
    | true =>
      simp only [d16285, d178347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d159762 q = 1) : d178348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d178348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d178348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d159762 q = 1) : d178349 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d178349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d178349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d159762 q = 1) : d178350 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d178350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d178350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d159762 q = 1) : d178351 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d178351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d178351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d159762 q = 1) : d178352 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d178352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d178352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro40241 (p : Pattern) (ha : d16314 p = 1) (hb : d159762 p = 1) : d178358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d159762 q = 1) : d178355 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d178355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d178355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d159762 q = 1) : d178356 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d178356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d178356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d159762 q = 1) : d178357 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d178357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d178357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d159762 q = 1) : d178358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d178358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d178358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro40242 (p : Pattern) (ha : d128274 p = 1) (hb : d159762 p = 1) : d178364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d159762 q = 1) : d178329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d178329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40235 q ha hb
    | true =>
      simp only [d16260, d178329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40233 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d159762 q = 1) : d178330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d178330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d178330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d159762 q = 1) : d178331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d178331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d178331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d159762 q = 1) : d178332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d178332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d178332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d159762 q = 1) : d178336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d178336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40236 q ha hb
    | true =>
      simp only [d16267, d178336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40234 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d159762 q = 1) : d178337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d178337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d178337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d159762 q = 1) : d178338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d178338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d178338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d159762 q = 1) : d178353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d178353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40240 q ha hb
    | true =>
      simp only [d16291, d178353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40228 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d159762 q = 1) : d178354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d178354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d178354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d159762 q = 1) : d178359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d178359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40241 q ha hb
    | true =>
      simp only [d16315, d178359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d159762 q = 1) : d178360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d178360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d178360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d159762 q = 1) : d178361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d178361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d178361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d159762 q = 1) : d178362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d178362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d178362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d159762 q = 1) : d178363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d178363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d178363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128274 q = 1) (hb : d159762 q = 1) : d178364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d178364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d178364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro40243 (p : Pattern) (ha : d916 p = 1) (hb : d159762 p = 1) : d160195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d159762 q = 1) : d160153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d159762 q = 1) : d160195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d160195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d160195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40244 (p : Pattern) (ha : d922 p = 1) (hb : d159762 p = 1) : d160201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d159762 q = 1) : d160162 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d159762 q = 1) : d160163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d159762 q = 1) : d160201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d160201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d160201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40245 (p : Pattern) (ha : d16321 p = 1) (hb : d159762 p = 1) : d178365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d159762 q = 1) : d178305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d159762 q = 1) : d178306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d178306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d159762 q = 1) : d178327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d178327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d178327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d159762 q = 1) : d178365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d178365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d178365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40246 (p : Pattern) (ha : d16326 p = 1) (hb : d159762 p = 1) : d178370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40217 q ha hb
    | true =>
      simp only [d774, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d159762 q = 1) : d178305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d178305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d159762 q = 1) : d178333 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d178333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d178333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d159762 q = 1) : d178334 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d178334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d178334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d159762 q = 1) : d178370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d178370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d178370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40247 (p : Pattern) (ha : d16330 p = 1) (hb : d159762 p = 1) : d178374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d159762 q = 1) : d178347 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d178347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40239 q ha hb
    | true =>
      simp only [d16285, d178347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d159762 q = 1) : d178348 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d178348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d178348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d159762 q = 1) : d178349 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d178349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d178349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d159762 q = 1) : d178350 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d178350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d178350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d159762 q = 1) : d178351 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d178351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d178351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d159762 q = 1) : d178374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d178374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d178374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro40248 (p : Pattern) (ha : d16335 p = 1) (hb : d159762 p = 1) : d178377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d159762 q = 1) : d178303 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40227 q ha hb
    | true =>
      simp only [d16234, d178303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d159762 q = 1) : d178304 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d178304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d159762 q = 1) : d178355 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d178355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d178355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d159762 q = 1) : d178356 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d178356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d178356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d159762 q = 1) : d178357 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d178357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d178357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d159762 q = 1) : d178377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d178377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d178377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro40249 (p : Pattern) (ha : d128279 p = 1) (hb : d159762 p = 1) : d178383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d159762 q = 1) : d178329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d178329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40235 q ha hb
    | true =>
      simp only [d16260, d178329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40233 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d159762 q = 1) : d178330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d178330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d178330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d159762 q = 1) : d178331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d178331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d178331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d159762 q = 1) : d178332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d178332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d178332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d159762 q = 1) : d178336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d178336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40236 q ha hb
    | true =>
      simp only [d16267, d178336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40234 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d159762 q = 1) : d178337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d178337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d178337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d159762 q = 1) : d178338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d178338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d178338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d159762 q = 1) : d178353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d178353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40240 q ha hb
    | true =>
      simp only [d16291, d178353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40228 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d159762 q = 1) : d178354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d178354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d178354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d159762 q = 1) : d178359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d178359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40241 q ha hb
    | true =>
      simp only [d16315, d178359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d159762 q = 1) : d178360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d178360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d178360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d159762 q = 1) : d178361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d178361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d178361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d159762 q = 1) : d178362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d178362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d178362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d159762 q = 1) : d178363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d178363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d178363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d159762 q = 1) : d178366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d178366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40245 q ha hb
    | true =>
      simp only [d16322, d178366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40243 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d159762 q = 1) : d178367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d178367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d178367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d159762 q = 1) : d178368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d178368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d178368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d159762 q = 1) : d178369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d178369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d178369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d159762 q = 1) : d178371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d178371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40246 q ha hb
    | true =>
      simp only [d16327, d178371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40244 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d159762 q = 1) : d178372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d178372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d178372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d159762 q = 1) : d178373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d178373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d178373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d159762 q = 1) : d178375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d178375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40247 q ha hb
    | true =>
      simp only [d16331, d178375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40230 q ha hb
  have h23 (q : Pattern) (ha : d128275 q = 1) (hb : d159762 q = 1) : d178376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d178376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128275, d178376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d159762 q = 1) : d178378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d178378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40248 q ha hb
    | true =>
      simp only [d16336, d178378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d159762 q = 1) : d178379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d178379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d178379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128276 q = 1) (hb : d159762 q = 1) : d178380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d178380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d178380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128277 q = 1) (hb : d159762 q = 1) : d178381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d178381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128277, d178381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128278 q = 1) (hb : d159762 q = 1) : d178382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d178382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128278, d178382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128279 q = 1) (hb : d159762 q = 1) : d178383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d178383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d178383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
end NetHack.Soko22Hazard87
